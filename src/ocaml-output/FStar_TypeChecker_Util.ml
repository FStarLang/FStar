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
        let uu____419 = FStar_Options.push ()  in
        let uu____420 =
          FStar_Options.set_option "hide_uvar_nums"
            (FStar_Options.Bool false)
           in
        let uu____421 =
          FStar_Options.set_option "print_implicits"
            (FStar_Options.Bool true)
           in
        let uu____422 =
          let uu____423 =
            let uu____428 =
              let uu____429 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____429
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____428)  in
          FStar_Errors.log_issue r uu____423  in
        FStar_Options.pop ()
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
                      let uu____522 =
                        let uu____523 =
                          FStar_Syntax_Subst.compress
                            a.FStar_Syntax_Syntax.sort
                           in
                        uu____523.FStar_Syntax_Syntax.n  in
                      match uu____522 with
                      | FStar_Syntax_Syntax.Tm_unknown  ->
                          let uu____530 = FStar_Syntax_Util.type_u ()  in
                          (match uu____530 with
                           | (k,uu____540) ->
                               let t2 =
                                 let uu____542 =
                                   FStar_TypeChecker_Rel.new_uvar
                                     e1.FStar_Syntax_Syntax.pos scope k
                                    in
                                 FStar_All.pipe_right uu____542
                                   FStar_Pervasives_Native.fst
                                  in
                               ((let uu___97_552 = a  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___97_552.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___97_552.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t2
                                 }), false))
                      | uu____553 -> (a, true)  in
                    let rec aux must_check_ty vars e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____593) ->
                          aux must_check_ty vars e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____600) ->
                          ((FStar_Pervasives_Native.fst t2), true)
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____663) ->
                          let uu____684 =
                            FStar_All.pipe_right bs
                              (FStar_List.fold_left
                                 (fun uu____744  ->
                                    fun uu____745  ->
                                      match (uu____744, uu____745) with
                                      | ((scope,bs1,must_check_ty1),(a,imp))
                                          ->
                                          let uu____823 =
                                            if must_check_ty1
                                            then (a, true)
                                            else mk_binder1 scope a  in
                                          (match uu____823 with
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
                          (match uu____684 with
                           | (scope,bs1,must_check_ty1) ->
                               let uu____935 = aux must_check_ty1 scope body
                                  in
                               (match uu____935 with
                                | (res,must_check_ty2) ->
                                    let c =
                                      match res with
                                      | FStar_Util.Inl t2 ->
                                          let uu____964 =
                                            FStar_Options.ml_ish ()  in
                                          if uu____964
                                          then FStar_Syntax_Util.ml_comp t2 r
                                          else
                                            FStar_Syntax_Syntax.mk_Total t2
                                      | FStar_Util.Inr c -> c  in
                                    let t2 = FStar_Syntax_Util.arrow bs1 c
                                       in
                                    let uu____970 =
                                      let uu____971 =
                                        FStar_TypeChecker_Env.debug env1
                                          FStar_Options.High
                                         in
                                      if uu____971
                                      then
                                        let uu____972 =
                                          FStar_Range.string_of_range r  in
                                        let uu____973 =
                                          FStar_Syntax_Print.term_to_string
                                            t2
                                           in
                                        let uu____974 =
                                          FStar_Util.string_of_bool
                                            must_check_ty2
                                           in
                                        FStar_Util.print3
                                          "(%s) Using type %s .... must check = %s\n"
                                          uu____972 uu____973 uu____974
                                      else ()  in
                                    ((FStar_Util.Inl t2), must_check_ty2)))
                      | uu____984 ->
                          if must_check_ty
                          then
                            ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                          else
                            (let uu____998 =
                               let uu____1003 =
                                 let uu____1004 =
                                   FStar_TypeChecker_Rel.new_uvar r vars
                                     FStar_Syntax_Util.ktype0
                                    in
                                 FStar_All.pipe_right uu____1004
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_Util.Inl uu____1003  in
                             (uu____998, false))
                       in
                    let uu____1017 =
                      let uu____1026 = t_binders env1  in
                      aux false uu____1026 e1  in
                    (match uu____1017 with
                     | (t2,b) ->
                         let t3 =
                           match t2 with
                           | FStar_Util.Inr c ->
                               let uu____1051 =
                                 FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                               if uu____1051
                               then FStar_Syntax_Util.comp_result c
                               else
                                 (let uu____1055 =
                                    let uu____1060 =
                                      let uu____1061 =
                                        FStar_Syntax_Print.comp_to_string c
                                         in
                                      FStar_Util.format1
                                        "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                        uu____1061
                                       in
                                    (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                      uu____1060)
                                     in
                                  FStar_Errors.raise_error uu____1055 rng)
                           | FStar_Util.Inl t3 -> t3  in
                         (univ_vars2, t3, b)))
           | uu____1067 ->
               let uu____1068 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____1068 with
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
            let uu____1158 =
              let uu____1163 =
                FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
              match uu____1163 with
              | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____1168;
                  FStar_Syntax_Syntax.vars = uu____1169;_} ->
                  let uu____1172 = FStar_Syntax_Util.type_u ()  in
                  (match uu____1172 with
                   | (t,uu____1182) ->
                       let uu____1183 = new_uvar env1 t  in
                       (uu____1183, FStar_TypeChecker_Rel.trivial_guard))
              | t -> tc_annot env1 t  in
            match uu____1158 with
            | (t_x,guard) ->
                ((let uu___98_1192 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___98_1192.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___98_1192.FStar_Syntax_Syntax.index);
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
                  | uu____1264 ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant c)
                        FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                   in
                ([], [], [], env1, e, FStar_TypeChecker_Rel.trivial_guard,
                  p1)
            | FStar_Syntax_Syntax.Pat_dot_term (x,uu____1272) ->
                let uu____1277 = FStar_Syntax_Util.type_u ()  in
                (match uu____1277 with
                 | (k,uu____1303) ->
                     let t = new_uvar env1 k  in
                     let x1 =
                       let uu___99_1306 = x  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___99_1306.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___99_1306.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = t
                       }  in
                     let uu____1307 =
                       let uu____1312 =
                         FStar_TypeChecker_Env.all_binders env1  in
                       FStar_TypeChecker_Rel.new_uvar
                         p1.FStar_Syntax_Syntax.p uu____1312 t
                        in
                     (match uu____1307 with
                      | (e,u) ->
                          let p2 =
                            let uu___100_1338 = p1  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                              FStar_Syntax_Syntax.p =
                                (uu___100_1338.FStar_Syntax_Syntax.p)
                            }  in
                          ([], [], [], env1, e,
                            FStar_TypeChecker_Rel.trivial_guard, p2)))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let uu____1348 = check_bv env1 x  in
                (match uu____1348 with
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
                let uu____1389 = check_bv env1 x  in
                (match uu____1389 with
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
                let uu____1446 =
                  FStar_All.pipe_right pats
                    (FStar_List.fold_left
                       (fun uu____1582  ->
                          fun uu____1583  ->
                            match (uu____1582, uu____1583) with
                            | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                                let uu____1781 =
                                  pat_as_arg_with_env allow_wc_dependence
                                    env2 p2
                                   in
                                (match uu____1781 with
                                 | (b',a',w',env3,te,guard',pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te  in
                                     let uu____1857 =
                                       FStar_TypeChecker_Rel.conj_guard guard
                                         guard'
                                        in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), uu____1857, ((pat, imp)
                                       :: pats1))))
                       ([], [], [], env1, [],
                         FStar_TypeChecker_Rel.trivial_guard, []))
                   in
                (match uu____1446 with
                 | (b,a,w,env2,args,guard,pats1) ->
                     let e =
                       let uu____1988 =
                         let uu____1991 = FStar_Syntax_Syntax.fv_to_tm fv  in
                         let uu____1992 =
                           FStar_All.pipe_right args FStar_List.rev  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____1991 uu____1992
                          in
                       uu____1988 FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     let uu____1999 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten
                        in
                     let uu____2010 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten
                        in
                     let uu____2021 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten
                        in
                     (uu____1999, uu____2010, uu____2021, env2, e, guard,
                       (let uu___101_2043 = p1  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___101_2043.FStar_Syntax_Syntax.p)
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
                    (fun uu____2132  ->
                       match uu____2132 with
                       | (p2,imp) ->
                           let uu____2151 = elaborate_pat env1 p2  in
                           (uu____2151, imp)) pats
                   in
                let uu____2156 =
                  FStar_TypeChecker_Env.lookup_datacon env1
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____2156 with
                 | (uu____2163,t) ->
                     let uu____2165 = FStar_Syntax_Util.arrow_formals t  in
                     (match uu____2165 with
                      | (f,uu____2181) ->
                          let rec aux formals pats2 =
                            match (formals, pats2) with
                            | ([],[]) -> []
                            | ([],uu____2305::uu____2306) ->
                                let uu____2349 =
                                  FStar_Ident.range_of_lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_TooManyPatternArguments,
                                    "Too many pattern arguments") uu____2349
                            | (uu____2358::uu____2359,[]) ->
                                FStar_All.pipe_right formals
                                  (FStar_List.map
                                     (fun uu____2437  ->
                                        match uu____2437 with
                                        | (t1,imp) ->
                                            (match imp with
                                             | FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Syntax.Implicit
                                                 inaccessible) ->
                                                 let a =
                                                   let uu____2464 =
                                                     let uu____2467 =
                                                       FStar_Syntax_Syntax.range_of_bv
                                                         t1
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____2467
                                                      in
                                                   FStar_Syntax_Syntax.new_bv
                                                     uu____2464
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let r =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 let uu____2469 =
                                                   maybe_dot inaccessible a r
                                                    in
                                                 (uu____2469, true)
                                             | uu____2474 ->
                                                 let uu____2477 =
                                                   let uu____2482 =
                                                     let uu____2483 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1
                                                        in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____2483
                                                      in
                                                   (FStar_Errors.Fatal_InsufficientPatternArguments,
                                                     uu____2482)
                                                    in
                                                 let uu____2484 =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____2477 uu____2484)))
                            | (f1::formals',(p2,p_imp)::pats') ->
                                (match f1 with
                                 | (uu____2558,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    uu____2559)) when p_imp ->
                                     let uu____2562 = aux formals' pats'  in
                                     (p2, true) :: uu____2562
                                 | (uu____2579,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    inaccessible)) ->
                                     let a =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p2.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     let p3 =
                                       let uu____2587 =
                                         FStar_Ident.range_of_lid
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          in
                                       maybe_dot inaccessible a uu____2587
                                        in
                                     let uu____2588 = aux formals' pats2  in
                                     (p3, true) :: uu____2588
                                 | (uu____2605,imp) ->
                                     let uu____2611 =
                                       let uu____2618 =
                                         FStar_Syntax_Syntax.is_implicit imp
                                          in
                                       (p2, uu____2618)  in
                                     let uu____2621 = aux formals' pats'  in
                                     uu____2611 :: uu____2621)
                             in
                          let uu___102_2636 = p1  in
                          let uu____2639 =
                            let uu____2640 =
                              let uu____2653 = aux f pats1  in
                              (fv, uu____2653)  in
                            FStar_Syntax_Syntax.Pat_cons uu____2640  in
                          {
                            FStar_Syntax_Syntax.v = uu____2639;
                            FStar_Syntax_Syntax.p =
                              (uu___102_2636.FStar_Syntax_Syntax.p)
                          }))
            | uu____2670 -> p1  in
          let one_pat allow_wc_dependence env1 p1 =
            let p2 = elaborate_pat env1 p1  in
            let uu____2709 = pat_as_arg_with_env allow_wc_dependence env1 p2
               in
            match uu____2709 with
            | (b,a,w,env2,arg,guard,p3) ->
                let uu____2767 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                   in
                (match uu____2767 with
                 | FStar_Pervasives_Native.Some x ->
                     let uu____2793 =
                       FStar_TypeChecker_Err.nonlinear_pattern_variable x  in
                     FStar_Errors.raise_error uu____2793
                       p3.FStar_Syntax_Syntax.p
                 | uu____2816 -> (b, a, w, arg, guard, p3))
             in
          let uu____2825 = one_pat true env p  in
          match uu____2825 with
          | (b,uu____2855,uu____2856,tm,guard,p1) -> (b, tm, guard, p1)
  
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
          | (uu____2911,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2913)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____2918,uu____2919) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              let uu____2922 =
                if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
                then
                  let uu____2923 =
                    let uu____2924 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2925 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2924 uu____2925
                     in
                  failwith uu____2923
                else ()  in
              let uu____2927 =
                let uu____2928 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat")
                   in
                if uu____2928
                then
                  let uu____2929 = FStar_Syntax_Print.bv_to_string x  in
                  let uu____2930 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2929
                    uu____2930
                else ()  in
              let s =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.Beta] env
                  y.FStar_Syntax_Syntax.sort
                 in
              let x1 =
                let uu___103_2934 = x  in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___103_2934.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___103_2934.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = s
                }  in
              pkg (FStar_Syntax_Syntax.Pat_var x1)
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              let uu____2937 =
                let uu____2938 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation
                   in
                if uu____2938
                then
                  let uu____2939 =
                    let uu____2940 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2941 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2940 uu____2941
                     in
                  failwith uu____2939
                else ()  in
              let s =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.Beta] env
                  y.FStar_Syntax_Syntax.sort
                 in
              let x1 =
                let uu___104_2945 = x  in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___104_2945.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___104_2945.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = s
                }  in
              pkg (FStar_Syntax_Syntax.Pat_wild x1)
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2947),uu____2948) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              let uu____2969 =
                let uu____2970 =
                  let uu____2971 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  Prims.op_Negation uu____2971  in
                if uu____2970
                then
                  let uu____2972 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____2972
                else ()  in
              pkg (FStar_Syntax_Syntax.Pat_cons (fv', []))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____2991;
                FStar_Syntax_Syntax.vars = uu____2992;_},args))
              ->
              let uu____3030 =
                let uu____3031 =
                  let uu____3032 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____3032 Prims.op_Negation  in
                if uu____3031
                then
                  let uu____3033 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3033
                else ()  in
              let fv1 = fv'  in
              let rec match_args matched_pats args1 argpats1 =
                match (args1, argpats1) with
                | ([],[]) ->
                    pkg
                      (FStar_Syntax_Syntax.Pat_cons
                         (fv1, (FStar_List.rev matched_pats)))
                | (arg::args2,(argpat,uu____3172)::argpats2) ->
                    (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                     | ((e2,FStar_Pervasives_Native.Some
                         (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                        uu____3247) ->
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
                     | ((e2,imp),uu____3284) ->
                         let pat =
                           let uu____3306 = aux argpat e2  in
                           let uu____3307 =
                             FStar_Syntax_Syntax.is_implicit imp  in
                           (uu____3306, uu____3307)  in
                         match_args (pat :: matched_pats) args2 argpats2)
                | uu____3312 ->
                    let uu____3335 =
                      let uu____3336 = FStar_Syntax_Print.pat_to_string p1
                         in
                      let uu____3337 = FStar_Syntax_Print.term_to_string e1
                         in
                      FStar_Util.format2
                        "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                        uu____3336 uu____3337
                       in
                    failwith uu____3335
                 in
              match_args [] args argpats
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____3349;
                     FStar_Syntax_Syntax.vars = uu____3350;_},uu____3351);
                FStar_Syntax_Syntax.pos = uu____3352;
                FStar_Syntax_Syntax.vars = uu____3353;_},args))
              ->
              let uu____3395 =
                let uu____3396 =
                  let uu____3397 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____3397 Prims.op_Negation  in
                if uu____3396
                then
                  let uu____3398 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3398
                else ()  in
              let fv1 = fv'  in
              let rec match_args matched_pats args1 argpats1 =
                match (args1, argpats1) with
                | ([],[]) ->
                    pkg
                      (FStar_Syntax_Syntax.Pat_cons
                         (fv1, (FStar_List.rev matched_pats)))
                | (arg::args2,(argpat,uu____3537)::argpats2) ->
                    (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                     | ((e2,FStar_Pervasives_Native.Some
                         (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                        uu____3612) ->
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
                     | ((e2,imp),uu____3649) ->
                         let pat =
                           let uu____3671 = aux argpat e2  in
                           let uu____3672 =
                             FStar_Syntax_Syntax.is_implicit imp  in
                           (uu____3671, uu____3672)  in
                         match_args (pat :: matched_pats) args2 argpats2)
                | uu____3677 ->
                    let uu____3700 =
                      let uu____3701 = FStar_Syntax_Print.pat_to_string p1
                         in
                      let uu____3702 = FStar_Syntax_Print.term_to_string e1
                         in
                      FStar_Util.format2
                        "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                        uu____3701 uu____3702
                       in
                    failwith uu____3700
                 in
              match_args [] args argpats
          | uu____3711 ->
              let uu____3716 =
                let uu____3717 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p  in
                let uu____3718 = FStar_Syntax_Print.pat_to_string qq  in
                let uu____3719 = FStar_Syntax_Print.term_to_string exp  in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____3717 uu____3718 uu____3719
                 in
              failwith uu____3716
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
    let pat_as_arg uu____3760 =
      match uu____3760 with
      | (p,i) ->
          let uu____3777 = decorated_pattern_as_term p  in
          (match uu____3777 with
           | (vars,te) ->
               let uu____3800 =
                 let uu____3805 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____3805)  in
               (vars, uu____3800))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____3819 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____3819)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____3823 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____3823)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____3827 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____3827)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____3848 =
          let uu____3863 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____3863 FStar_List.unzip  in
        (match uu____3848 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____3973 =
               let uu____3974 =
                 let uu____3975 =
                   let uu____3990 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____3990, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____3975  in
               mk1 uu____3974  in
             (vars1, uu____3973))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____4022,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____4032,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____4046 -> FStar_Pervasives_Native.Some hd1)
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____4072)::[] -> wp
      | uu____4089 ->
          let uu____4098 =
            let uu____4099 =
              let uu____4100 =
                FStar_List.map
                  (fun uu____4110  ->
                     match uu____4110 with
                     | (x,uu____4116) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____4100 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____4099
             in
          failwith uu____4098
       in
    let uu____4121 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____4121, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____4141 = destruct_comp c  in
        match uu____4141 with
        | (u,uu____4149,wp) ->
            let uu____4151 =
              let uu____4160 =
                let uu____4161 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____4161  in
              [uu____4160]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____4151;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____4177 =
          let uu____4184 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____4185 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____4184 uu____4185  in
        match uu____4177 with | (m,uu____4187,uu____4188) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____4204 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____4204
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
        let uu____4247 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____4247 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____4284 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____4284 with
             | (a,kwp) ->
                 let uu____4315 = destruct_comp m1  in
                 let uu____4322 = destruct_comp m2  in
                 ((md, a, kwp), uu____4315, uu____4322))
  
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
            let uu____4402 =
              let uu____4403 =
                let uu____4412 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____4412]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4403;
                FStar_Syntax_Syntax.flags = flags1
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4402
  
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
          let uu____4466 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____4466
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
      let uu____4478 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____4478
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____4481  ->
           let uu____4482 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____4482)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4488 =
      let uu____4489 = FStar_Syntax_Subst.compress t  in
      uu____4489.FStar_Syntax_Syntax.n  in
    match uu____4488 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4492 -> true
    | uu____4505 -> false
  
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
              let uu____4560 =
                let uu____4561 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____4561  in
              if uu____4560
              then f
              else (let uu____4563 = reason1 ()  in label uu____4563 r f)
  
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
            let uu___105_4580 = g  in
            let uu____4581 =
              let uu____4582 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____4582  in
            {
              FStar_TypeChecker_Env.guard_f = uu____4581;
              FStar_TypeChecker_Env.deferred =
                (uu___105_4580.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___105_4580.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___105_4580.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4602 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4602
        then c
        else
          (let uu____4604 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____4604
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4648 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____4648]  in
                       let us =
                         let uu____4652 =
                           let uu____4655 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____4655]  in
                         u_res :: uu____4652  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____4659 =
                         let uu____4662 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____4663 =
                           let uu____4664 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____4665 =
                             let uu____4668 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____4669 =
                               let uu____4672 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____4672]  in
                             uu____4668 :: uu____4669  in
                           uu____4664 :: uu____4665  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4662 uu____4663
                          in
                       uu____4659 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____4676 = destruct_comp c1  in
              match uu____4676 with
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
          (fun uu____4709  ->
             let uu____4710 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____4710)
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___78_4719  ->
            match uu___78_4719 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____4720 -> false))
  
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
                (let uu____4742 =
                   FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ
                    in
                 Prims.op_Negation uu____4742))
               &&
               (let uu____4749 = FStar_Syntax_Util.head_and_args' e  in
                match uu____4749 with
                | (head1,uu____4763) ->
                    let uu____4780 =
                      let uu____4781 = FStar_Syntax_Util.un_uinst head1  in
                      uu____4781.FStar_Syntax_Syntax.n  in
                    (match uu____4780 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____4785 =
                           let uu____4786 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____4786
                            in
                         Prims.op_Negation uu____4785
                     | uu____4787 -> true)))
              &&
              (let uu____4789 = should_not_inline_lc lc  in
               Prims.op_Negation uu____4789)
  
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
            let uu____4815 =
              let uu____4816 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____4816  in
            if uu____4815
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____4818 = FStar_Syntax_Util.is_unit t  in
               if uu____4818
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
                    let uu____4824 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____4824
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____4826 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____4826 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____4834 =
                             let uu____4835 =
                               let uu____4838 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____4839 =
                                 let uu____4840 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____4841 =
                                   let uu____4844 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____4844]  in
                                 uu____4840 :: uu____4841  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____4838
                                 uu____4839
                                in
                             uu____4835 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.NoFullNorm] env
                             uu____4834)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          let uu____4847 =
            let uu____4848 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Return")
               in
            if uu____4848
            then
              let uu____4849 =
                FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
              let uu____4850 = FStar_Syntax_Print.term_to_string v1  in
              let uu____4851 =
                FStar_TypeChecker_Normalize.comp_to_string env c  in
              FStar_Util.print3 "(%s) returning %s at comp type %s\n"
                uu____4849 uu____4850 uu____4851
            else ()  in
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    let uu____4864 =
      FStar_All.pipe_right flags1
        (FStar_Util.for_some
           (fun uu___79_4868  ->
              match uu___79_4868 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____4869 -> false))
       in
    if uu____4864
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags1
        (FStar_List.collect
           (fun uu___80_4878  ->
              match uu___80_4878 with
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
        let uu____4897 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4897
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____4900 = destruct_comp c1  in
           match uu____4900 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____4914 =
                   let uu____4917 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____4918 =
                     let uu____4919 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____4920 =
                       let uu____4923 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____4924 =
                         let uu____4927 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____4927]  in
                       uu____4923 :: uu____4924  in
                     uu____4919 :: uu____4920  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4917 uu____4918  in
                 uu____4914 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____4930 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t wp1 uu____4930)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____4952 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____4954 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____4954
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____4957 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____4957 weaken
  
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
               let uu____5000 = destruct_comp c1  in
               match uu____5000 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____5014 =
                       let uu____5017 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____5018 =
                         let uu____5019 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____5020 =
                           let uu____5023 =
                             let uu____5024 =
                               let uu____5025 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____5025 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____5024
                              in
                           let uu____5026 =
                             let uu____5029 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____5029]  in
                           uu____5023 :: uu____5026  in
                         uu____5019 :: uu____5020  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5017 uu____5018
                        in
                     uu____5014 FStar_Pervasives_Native.None
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
            let uu____5074 = FStar_TypeChecker_Rel.is_trivial g0  in
            if uu____5074
            then (lc, g0)
            else
              (let flags1 =
                 let uu____5083 =
                   let uu____5090 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____5090
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5083 with
                 | (maybe_trivial_post,flags1) ->
                     let uu____5110 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___81_5118  ->
                               match uu___81_5118 with
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
                               | uu____5121 -> []))
                        in
                     FStar_List.append flags1 uu____5110
                  in
               let strengthen uu____5126 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____5130 = FStar_TypeChecker_Rel.guard_form g01  in
                    match uu____5130 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        let uu____5132 =
                          let uu____5133 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____5133
                          then
                            let uu____5134 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debug_only
                               in
                            let uu____5135 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____5134 uu____5135
                          else ()  in
                        strengthen_comp env reason c f flags1)
                  in
               let uu____5137 =
                 let uu____5138 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____5138
                   lc.FStar_Syntax_Syntax.res_typ flags1 strengthen
                  in
               (uu____5137,
                 (let uu___106_5140 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___106_5140.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___106_5140.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___106_5140.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___82_5147  ->
            match uu___82_5147 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____5148 -> false) lc.FStar_Syntax_Syntax.cflags)
  
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
          let uu____5173 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____5173
          then e
          else
            (let uu____5175 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____5177 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____5177)
                in
             if uu____5175
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
          fun uu____5225  ->
            match uu____5225 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____5244 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____5244 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____5252 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____5252
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags1 =
                       let uu____5259 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____5259
                       then
                         let uu____5262 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____5262
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5266 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____5266
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5271 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____5271
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____5275 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____5275
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags1
                     else flags1)
                   in
                let bind_it uu____5283 =
                  let uu____5284 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____5284
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
                     let uu____5289 =
                       debug1
                         (fun uu____5298  ->
                            let uu____5299 =
                              FStar_Syntax_Print.comp_to_string c1  in
                            let uu____5300 =
                              match b with
                              | FStar_Pervasives_Native.None  -> "none"
                              | FStar_Pervasives_Native.Some x ->
                                  FStar_Syntax_Print.bv_to_string x
                               in
                            let uu____5302 =
                              FStar_Syntax_Print.comp_to_string c2  in
                            FStar_Util.print3
                              "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                              uu____5299 uu____5300 uu____5302)
                        in
                     let aux uu____5315 =
                       let uu____5316 = FStar_Syntax_Util.is_trivial_wp c1
                          in
                       if uu____5316
                       then
                         match b with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Util.Inl (c2, "trivial no binder")
                         | FStar_Pervasives_Native.Some uu____5337 ->
                             let uu____5338 = FStar_Syntax_Util.is_ml_comp c2
                                in
                             (if uu____5338
                              then FStar_Util.Inl (c2, "trivial ml")
                              else
                                FStar_Util.Inr "c1 trivial; but c2 is not ML")
                       else
                         (let uu____5357 =
                            (FStar_Syntax_Util.is_ml_comp c1) &&
                              (FStar_Syntax_Util.is_ml_comp c2)
                             in
                          if uu____5357
                          then FStar_Util.Inl (c2, "both ml")
                          else
                            FStar_Util.Inr
                              "c1 not trivial, and both are not ML")
                        in
                     let subst_c2 e1opt1 reason =
                       match (e1opt1, b) with
                       | (FStar_Pervasives_Native.Some
                          e,FStar_Pervasives_Native.Some x) ->
                           let uu____5426 =
                             let uu____5431 =
                               FStar_Syntax_Subst.subst_comp
                                 [FStar_Syntax_Syntax.NT (x, e)] c2
                                in
                             (uu____5431, reason)  in
                           FStar_Util.Inl uu____5426
                       | uu____5438 -> aux ()  in
                     let try_simplify uu____5461 =
                       let rec maybe_close t x c =
                         let uu____5475 =
                           let uu____5476 =
                             FStar_TypeChecker_Normalize.unfold_whnf env t
                              in
                           uu____5476.FStar_Syntax_Syntax.n  in
                         match uu____5475 with
                         | FStar_Syntax_Syntax.Tm_refine (y,uu____5480) ->
                             maybe_close y.FStar_Syntax_Syntax.sort x c
                         | FStar_Syntax_Syntax.Tm_fvar fv when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.unit_lid
                             -> close_comp env [x] c
                         | uu____5486 -> c  in
                       let uu____5487 =
                         let uu____5488 =
                           FStar_TypeChecker_Env.try_lookup_effect_lid env
                             FStar_Parser_Const.effect_GTot_lid
                            in
                         FStar_Option.isNone uu____5488  in
                       if uu____5487
                       then
                         let uu____5499 =
                           (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                             (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                            in
                         (if uu____5499
                          then
                            FStar_Util.Inl
                              (c2, "Early in prims; we don't have bind yet")
                          else
                            (let uu____5513 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                 "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                               uu____5513))
                       else
                         (let uu____5523 =
                            (FStar_Syntax_Util.is_total_comp c1) &&
                              (FStar_Syntax_Util.is_total_comp c2)
                             in
                          if uu____5523
                          then subst_c2 e1opt "both total"
                          else
                            (let uu____5533 =
                               (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                 (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                in
                             if uu____5533
                             then
                               let uu____5542 =
                                 let uu____5547 =
                                   FStar_Syntax_Syntax.mk_GTotal
                                     (FStar_Syntax_Util.comp_result c2)
                                    in
                                 (uu____5547, "both gtot")  in
                               FStar_Util.Inl uu____5542
                             else
                               (match (e1opt, b) with
                                | (FStar_Pervasives_Native.Some
                                   e,FStar_Pervasives_Native.Some x) ->
                                    let uu____5571 =
                                      (FStar_Syntax_Util.is_total_comp c1) &&
                                        (let uu____5573 =
                                           FStar_Syntax_Syntax.is_null_bv x
                                            in
                                         Prims.op_Negation uu____5573)
                                       in
                                    if uu____5571
                                    then
                                      let c21 =
                                        FStar_Syntax_Subst.subst_comp
                                          [FStar_Syntax_Syntax.NT (x, e)] c2
                                         in
                                      let x1 =
                                        let uu___107_5584 = x  in
                                        {
                                          FStar_Syntax_Syntax.ppname =
                                            (uu___107_5584.FStar_Syntax_Syntax.ppname);
                                          FStar_Syntax_Syntax.index =
                                            (uu___107_5584.FStar_Syntax_Syntax.index);
                                          FStar_Syntax_Syntax.sort =
                                            (FStar_Syntax_Util.comp_result c1)
                                        }  in
                                      let uu____5585 =
                                        let uu____5590 =
                                          maybe_close
                                            x1.FStar_Syntax_Syntax.sort x1
                                            c21
                                           in
                                        (uu____5590, "c1 Tot")  in
                                      FStar_Util.Inl uu____5585
                                    else aux ()
                                | uu____5596 -> aux ())))
                        in
                     let uu____5605 = try_simplify ()  in
                     match uu____5605 with
                     | FStar_Util.Inl (c,reason) ->
                         let uu____5620 =
                           debug1
                             (fun uu____5625  ->
                                let uu____5626 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____5626)
                            in
                         c
                     | FStar_Util.Inr reason ->
                         let uu____5632 =
                           debug1
                             (fun uu____5635  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason)
                            in
                         let mk_bind c11 b1 c21 =
                           let uu____5653 = lift_and_destruct env c11 c21  in
                           match uu____5653 with
                           | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                               let bs =
                                 match b1 with
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____5710 =
                                       FStar_Syntax_Syntax.null_binder t1  in
                                     [uu____5710]
                                 | FStar_Pervasives_Native.Some x ->
                                     let uu____5712 =
                                       FStar_Syntax_Syntax.mk_binder x  in
                                     [uu____5712]
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
                                 let uu____5726 =
                                   FStar_Syntax_Syntax.as_arg r11  in
                                 let uu____5727 =
                                   let uu____5730 =
                                     FStar_Syntax_Syntax.as_arg t1  in
                                   let uu____5731 =
                                     let uu____5734 =
                                       FStar_Syntax_Syntax.as_arg t2  in
                                     let uu____5735 =
                                       let uu____5738 =
                                         FStar_Syntax_Syntax.as_arg wp1  in
                                       let uu____5739 =
                                         let uu____5742 =
                                           let uu____5743 = mk_lam wp2  in
                                           FStar_Syntax_Syntax.as_arg
                                             uu____5743
                                            in
                                         [uu____5742]  in
                                       uu____5738 :: uu____5739  in
                                     uu____5734 :: uu____5735  in
                                   uu____5730 :: uu____5731  in
                                 uu____5726 :: uu____5727  in
                               let wp =
                                 let uu____5747 =
                                   let uu____5750 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_t1; u_t2] env md
                                       md.FStar_Syntax_Syntax.bind_wp
                                      in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____5750
                                     wp_args
                                    in
                                 uu____5747 FStar_Pervasives_Native.None
                                   t2.FStar_Syntax_Syntax.pos
                                  in
                               mk_comp md u_t2 t2 wp bind_flags
                            in
                         let mk_seq c11 b1 c21 =
                           let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11
                              in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21
                              in
                           let uu____5772 =
                             FStar_TypeChecker_Env.join env
                               c12.FStar_Syntax_Syntax.effect_name
                               c22.FStar_Syntax_Syntax.effect_name
                              in
                           match uu____5772 with
                           | (m,uu____5780,lift2) ->
                               let c23 =
                                 let uu____5783 = lift_comp c22 m lift2  in
                                 FStar_Syntax_Syntax.mk_Comp uu____5783  in
                               let uu____5784 = destruct_comp c12  in
                               (match uu____5784 with
                                | (u1,t1,wp1) ->
                                    let md_pure_or_ghost =
                                      FStar_TypeChecker_Env.get_effect_decl
                                        env
                                        c12.FStar_Syntax_Syntax.effect_name
                                       in
                                    let vc1 =
                                      let uu____5798 =
                                        let uu____5801 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [u1] env md_pure_or_ghost
                                            md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                           in
                                        let uu____5802 =
                                          let uu____5803 =
                                            FStar_Syntax_Syntax.as_arg t1  in
                                          let uu____5804 =
                                            let uu____5807 =
                                              FStar_Syntax_Syntax.as_arg wp1
                                               in
                                            [uu____5807]  in
                                          uu____5803 :: uu____5804  in
                                        FStar_Syntax_Syntax.mk_Tm_app
                                          uu____5801 uu____5802
                                         in
                                      uu____5798 FStar_Pervasives_Native.None
                                        r1
                                       in
                                    strengthen_comp env
                                      FStar_Pervasives_Native.None c23 vc1
                                      bind_flags)
                            in
                         let c1_typ =
                           FStar_TypeChecker_Env.unfold_effect_abbrev env c1
                            in
                         let uu____5814 = destruct_comp c1_typ  in
                         (match uu____5814 with
                          | (u_res_t1,res_t1,uu____5823) ->
                              let uu____5824 =
                                (FStar_Option.isSome b) &&
                                  (should_return env e1opt lc11)
                                 in
                              if uu____5824
                              then
                                let e1 = FStar_Option.get e1opt  in
                                let x = FStar_Option.get b  in
                                let uu____5827 =
                                  FStar_Syntax_Util.is_partial_return c1  in
                                (if uu____5827
                                 then
                                   let uu____5828 =
                                     debug1
                                       (fun uu____5835  ->
                                          let uu____5836 =
                                            FStar_TypeChecker_Normalize.term_to_string
                                              env e1
                                             in
                                          let uu____5837 =
                                            FStar_Syntax_Print.bv_to_string x
                                             in
                                          FStar_Util.print2
                                            "(3) bind (case a): Substituting %s for %s"
                                            uu____5836 uu____5837)
                                      in
                                   let c21 =
                                     FStar_Syntax_Subst.subst_comp
                                       [FStar_Syntax_Syntax.NT (x, e1)] c2
                                      in
                                   mk_bind c1 b c21
                                 else
                                   (let uu____5840 =
                                      ((FStar_Options.vcgen_optimize_bind_as_seq
                                          ())
                                         &&
                                         (lcomp_has_trivial_postcondition
                                            lc11))
                                        &&
                                        (let uu____5842 =
                                           FStar_TypeChecker_Env.try_lookup_lid
                                             env
                                             FStar_Parser_Const.with_type_lid
                                            in
                                         FStar_Option.isSome uu____5842)
                                       in
                                    if uu____5840
                                    then
                                      let e1' =
                                        let uu____5864 =
                                          FStar_Options.vcgen_decorate_with_type
                                            ()
                                           in
                                        if uu____5864
                                        then
                                          FStar_Syntax_Util.mk_with_type
                                            u_res_t1 res_t1 e1
                                        else e1  in
                                      let uu____5868 =
                                        debug1
                                          (fun uu____5875  ->
                                             let uu____5876 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env e1'
                                                in
                                             let uu____5877 =
                                               FStar_Syntax_Print.bv_to_string
                                                 x
                                                in
                                             FStar_Util.print2
                                               "(3) bind (case b): Substituting %s for %s"
                                               uu____5876 uu____5877)
                                         in
                                      let c21 =
                                        FStar_Syntax_Subst.subst_comp
                                          [FStar_Syntax_Syntax.NT (x, e1')]
                                          c2
                                         in
                                      mk_seq c1 b c21
                                    else
                                      (let uu____5882 =
                                         debug1
                                           (fun uu____5889  ->
                                              let uu____5890 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____5891 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____5890 uu____5891)
                                          in
                                       let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       let x_eq_e =
                                         let uu____5894 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         FStar_Syntax_Util.mk_eq2 u_res_t1
                                           res_t1 e1 uu____5894
                                          in
                                       let c22 = weaken_comp env c21 x_eq_e
                                          in
                                       mk_bind c1 b c22)))
                              else mk_bind c1 b c2))
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
      | uu____5910 -> g2
  
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
            (let uu____5932 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____5932)
           in
        let flags1 =
          if should_return1
          then
            let uu____5938 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____5938
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____5947 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____5951 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____5951
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____5953 =
              let uu____5954 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____5954  in
            (if uu____5953
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___108_5957 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___108_5957.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___108_5957.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___108_5957.FStar_Syntax_Syntax.effect_args);
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
               let uu____5968 =
                 let uu____5971 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____5971
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5968
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____5976 =
               let uu____5977 =
                 let uu____5978 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____5978
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____5977  in
             FStar_Syntax_Util.comp_set_flags uu____5976 flags1)
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
            fun uu____6013  ->
              match uu____6013 with
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
                    let uu____6025 =
                      ((let uu____6028 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____6028) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____6025
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6042 =
        let uu____6043 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6043  in
      FStar_Syntax_Syntax.fvar uu____6042 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____6109  ->
                 match uu____6109 with
                 | (uu____6122,eff_label,uu____6124,uu____6125) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____6136 =
          let uu____6143 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____6177  ->
                    match uu____6177 with
                    | (uu____6190,uu____6191,flags1,uu____6193) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___83_6207  ->
                                match uu___83_6207 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____6208 -> false))))
             in
          if uu____6143
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____6136 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____6230 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____6232 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____6232
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____6257 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____6258 =
                     let uu____6261 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____6262 =
                       let uu____6263 = FStar_Syntax_Syntax.as_arg res_t1  in
                       let uu____6264 =
                         let uu____6267 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____6268 =
                           let uu____6271 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____6272 =
                             let uu____6275 = FStar_Syntax_Syntax.as_arg wp_e
                                in
                             [uu____6275]  in
                           uu____6271 :: uu____6272  in
                         uu____6267 :: uu____6268  in
                       uu____6263 :: uu____6264  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____6261 uu____6262  in
                   uu____6258 FStar_Pervasives_Native.None uu____6257  in
                 let default_case =
                   let post_k =
                     let uu____6282 =
                       let uu____6289 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____6289]  in
                     let uu____6290 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6282 uu____6290  in
                   let kwp =
                     let uu____6296 =
                       let uu____6303 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____6303]  in
                     let uu____6304 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6296 uu____6304  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____6309 =
                       let uu____6310 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____6310]  in
                     let uu____6311 =
                       let uu____6312 =
                         let uu____6316 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____6316
                          in
                       let uu____6317 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____6312 uu____6317  in
                     FStar_Syntax_Util.abs uu____6309 uu____6311
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
                   let uu____6335 =
                     should_not_inline_whole_match ||
                       (let uu____6337 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____6337)
                      in
                   if uu____6335 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____6370  ->
                        fun celse  ->
                          match uu____6370 with
                          | (g,eff_label,uu____6386,cthen) ->
                              let uu____6398 =
                                let uu____6423 =
                                  let uu____6424 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____6424
                                   in
                                lift_and_destruct env uu____6423 celse  in
                              (match uu____6398 with
                               | ((md,uu____6426,uu____6427),(uu____6428,uu____6429,wp_then),
                                  (uu____6431,uu____6432,wp_else)) ->
                                   let uu____6452 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____6452 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____6466::[] -> comp
                 | uu____6506 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____6524 = destruct_comp comp1  in
                     (match uu____6524 with
                      | (uu____6531,uu____6532,wp) ->
                          let wp1 =
                            let uu____6537 =
                              let uu____6540 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____6541 =
                                let uu____6542 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____6543 =
                                  let uu____6546 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____6546]  in
                                uu____6542 :: uu____6543  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____6540
                                uu____6541
                               in
                            uu____6537 FStar_Pervasives_Native.None
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
          let uu____6581 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____6581 with
          | FStar_Pervasives_Native.None  ->
              let uu____6590 =
                FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                  env e c c'
                 in
              let uu____6595 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____6590 uu____6595
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
            let uu____6637 =
              let uu____6638 = FStar_Syntax_Subst.compress t2  in
              uu____6638.FStar_Syntax_Syntax.n  in
            match uu____6637 with
            | FStar_Syntax_Syntax.Tm_type uu____6641 -> true
            | uu____6642 -> false  in
          let uu____6643 =
            let uu____6644 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ  in
            uu____6644.FStar_Syntax_Syntax.n  in
          match uu____6643 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____6652 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid
                 in
              let b2t1 =
                let uu____6662 =
                  FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                    e.FStar_Syntax_Syntax.pos
                   in
                FStar_Syntax_Syntax.fvar uu____6662
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None
                 in
              let lc1 =
                let uu____6664 =
                  let uu____6665 =
                    let uu____6666 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____6666
                     in
                  (FStar_Pervasives_Native.None, uu____6665)  in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____6664
                 in
              let e1 =
                let uu____6676 =
                  let uu____6679 =
                    let uu____6680 = FStar_Syntax_Syntax.as_arg e  in
                    [uu____6680]  in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____6679  in
                uu____6676 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos
                 in
              (e1, lc1)
          | uu____6685 -> (e, lc)
  
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
              (let uu____6722 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name
                  in
               match uu____6722 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____6745 -> false)
             in
          let gopt =
            if use_eq
            then
              let uu____6767 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t
                 in
              (uu____6767, false)
            else
              (let uu____6773 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____6773, true))
             in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____6784) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____6793 =
                  FStar_TypeChecker_Err.basic_type_error env
                    (FStar_Pervasives_Native.Some e) t
                    lc.FStar_Syntax_Syntax.res_typ
                   in
                FStar_Errors.raise_error uu____6793 e.FStar_Syntax_Syntax.pos
              else
                (let uu____6805 =
                   FStar_TypeChecker_Rel.subtype_fail env e
                     lc.FStar_Syntax_Syntax.res_typ t
                    in
                 (e,
                   (let uu___109_6807 = lc  in
                    {
                      FStar_Syntax_Syntax.eff_name =
                        (uu___109_6807.FStar_Syntax_Syntax.eff_name);
                      FStar_Syntax_Syntax.res_typ = t;
                      FStar_Syntax_Syntax.cflags =
                        (uu___109_6807.FStar_Syntax_Syntax.cflags);
                      FStar_Syntax_Syntax.comp_thunk =
                        (uu___109_6807.FStar_Syntax_Syntax.comp_thunk)
                    }), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____6812 = FStar_TypeChecker_Rel.guard_form g  in
              (match uu____6812 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___110_6820 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___110_6820.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___110_6820.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___110_6820.FStar_Syntax_Syntax.comp_thunk)
                     }  in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___111_6823 = g  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___111_6823.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___111_6823.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___111_6823.FStar_TypeChecker_Env.implicits)
                     }  in
                   let strengthen uu____6828 =
                     let uu____6829 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ())
                        in
                     if uu____6829
                     then FStar_Syntax_Syntax.lcomp_comp lc
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f
                           in
                        let uu____6832 =
                          let uu____6833 = FStar_Syntax_Subst.compress f1  in
                          uu____6833.FStar_Syntax_Syntax.n  in
                        match uu____6832 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____6836,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____6838;
                                          FStar_Syntax_Syntax.vars =
                                            uu____6839;_},uu____6840)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___112_6862 = lc  in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___112_6862.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___112_6862.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp_thunk =
                                  (uu___112_6862.FStar_Syntax_Syntax.comp_thunk)
                              }  in
                            FStar_Syntax_Syntax.lcomp_comp lc1
                        | uu____6863 ->
                            let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                            let uu____6865 =
                              let uu____6866 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____6866
                              then
                                let uu____6867 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____6868 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t
                                   in
                                let uu____6869 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c
                                   in
                                let uu____6870 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1
                                   in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____6867 uu____6868 uu____6869 uu____6870
                              else ()  in
                            let u_t_opt = comp_univ_opt c  in
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
                                let uu____6883 =
                                  let uu____6886 =
                                    let uu____6887 =
                                      FStar_Syntax_Syntax.as_arg xexp  in
                                    [uu____6887]  in
                                  FStar_Syntax_Syntax.mk_Tm_app f1 uu____6886
                                   in
                                uu____6883 FStar_Pervasives_Native.None
                                  f1.FStar_Syntax_Syntax.pos
                              else f1  in
                            let uu____6891 =
                              let uu____6896 =
                                FStar_All.pipe_left
                                  (fun _0_17  ->
                                     FStar_Pervasives_Native.Some _0_17)
                                  (FStar_TypeChecker_Err.subtyping_failed env
                                     lc.FStar_Syntax_Syntax.res_typ t)
                                 in
                              let uu____6913 =
                                FStar_TypeChecker_Env.set_range env
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____6914 =
                                FStar_Syntax_Util.lcomp_of_comp cret  in
                              let uu____6915 =
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.guard_of_guard_formula
                                  (FStar_TypeChecker_Common.NonTrivial guard)
                                 in
                              strengthen_precondition uu____6896 uu____6913 e
                                uu____6914 uu____6915
                               in
                            (match uu____6891 with
                             | (eq_ret,_trivial_so_ok_to_discard) ->
                                 let x1 =
                                   let uu___113_6919 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___113_6919.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___113_6919.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort =
                                       (lc.FStar_Syntax_Syntax.res_typ)
                                   }  in
                                 let c1 =
                                   let uu____6921 =
                                     FStar_Syntax_Util.lcomp_of_comp c  in
                                   bind e.FStar_Syntax_Syntax.pos env
                                     (FStar_Pervasives_Native.Some e)
                                     uu____6921
                                     ((FStar_Pervasives_Native.Some x1),
                                       eq_ret)
                                    in
                                 let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                    in
                                 let uu____6925 =
                                   let uu____6926 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       FStar_Options.Extreme
                                      in
                                   if uu____6926
                                   then
                                     let uu____6927 =
                                       FStar_TypeChecker_Normalize.comp_to_string
                                         env c2
                                        in
                                     FStar_Util.print1 "Strengthened to %s\n"
                                       uu____6927
                                   else ()  in
                                 c2))
                      in
                   let flags1 =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___84_6937  ->
                             match uu___84_6937 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____6940 -> []))
                      in
                   let lc1 =
                     let uu____6942 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name
                        in
                     FStar_Syntax_Syntax.mk_lcomp uu____6942 t flags1
                       strengthen
                      in
                   let g2 =
                     let uu___114_6944 = g1  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___114_6944.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___114_6944.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___114_6944.FStar_TypeChecker_Env.implicits)
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
        let uu____6973 =
          let uu____6974 =
            let uu____6977 =
              let uu____6978 =
                let uu____6979 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____6979  in
              [uu____6978]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____6977  in
          uu____6974 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____6973  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t
         in
      let uu____6987 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____6987
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____7005 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____7020 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____7036 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____7036
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____7050)::(ens,uu____7052)::uu____7053 ->
                    let uu____7082 =
                      let uu____7085 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____7085  in
                    let uu____7086 =
                      let uu____7087 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____7087  in
                    (uu____7082, uu____7086)
                | uu____7090 ->
                    let uu____7099 =
                      let uu____7104 =
                        let uu____7105 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____7105
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____7104)
                       in
                    FStar_Errors.raise_error uu____7099
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____7121)::uu____7122 ->
                    let uu____7141 =
                      let uu____7146 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____7146
                       in
                    (match uu____7141 with
                     | (us_r,uu____7178) ->
                         let uu____7179 =
                           let uu____7184 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____7184
                            in
                         (match uu____7179 with
                          | (us_e,uu____7216) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____7219 =
                                  let uu____7220 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____7220
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____7219
                                  us_r
                                 in
                              let as_ens =
                                let uu____7222 =
                                  let uu____7223 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____7223
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____7222
                                  us_e
                                 in
                              let req =
                                let uu____7227 =
                                  let uu____7230 =
                                    let uu____7231 =
                                      let uu____7242 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____7242]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____7231
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____7230
                                   in
                                uu____7227 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____7260 =
                                  let uu____7263 =
                                    let uu____7264 =
                                      let uu____7275 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____7275]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____7264
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____7263
                                   in
                                uu____7260 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____7290 =
                                let uu____7293 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____7293  in
                              let uu____7294 =
                                let uu____7295 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____7295  in
                              (uu____7290, uu____7294)))
                | uu____7298 -> failwith "Impossible"))
  
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
      let uu____7327 =
        let uu____7328 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "SMTEncodingReify")
           in
        if uu____7328
        then
          let uu____7329 = FStar_Syntax_Print.term_to_string tm  in
          let uu____7330 = FStar_Syntax_Print.term_to_string tm'  in
          FStar_Util.print2 "Reified body %s \nto %s\n" uu____7329 uu____7330
        else ()  in
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
        let uu____7353 =
          let uu____7354 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "SMTEncodingReify")
             in
          if uu____7354
          then
            let uu____7355 = FStar_Syntax_Print.term_to_string tm  in
            let uu____7356 = FStar_Syntax_Print.term_to_string tm'  in
            FStar_Util.print2 "Reified body %s \nto %s\n" uu____7355
              uu____7356
          else ()  in
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____7363 =
      let uu____7364 =
        let uu____7365 = FStar_Syntax_Subst.compress t  in
        uu____7365.FStar_Syntax_Syntax.n  in
      match uu____7364 with
      | FStar_Syntax_Syntax.Tm_app uu____7368 -> false
      | uu____7383 -> true  in
    if uu____7363
    then t
    else
      (let uu____7385 = FStar_Syntax_Util.head_and_args t  in
       match uu____7385 with
       | (head1,args) ->
           let uu____7422 =
             let uu____7423 =
               let uu____7424 = FStar_Syntax_Subst.compress head1  in
               uu____7424.FStar_Syntax_Syntax.n  in
             match uu____7423 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____7427 -> false  in
           if uu____7422
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____7449 ->
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
             let uu____7493 = FStar_Syntax_Util.arrow_formals t1  in
             match uu____7493 with
             | (formals,uu____7507) ->
                 let n_implicits =
                   let uu____7525 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____7601  ->
                             match uu____7601 with
                             | (uu____7608,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality))))
                      in
                   match uu____7525 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits
                    in
                 n_implicits
              in
           let inst_n_binders t1 =
             let uu____7740 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____7740 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t  in
                 let n_available = number_of_implicits t1  in
                 if n_available < n_expected
                 then
                   let uu____7764 =
                     let uu____7769 =
                       let uu____7770 = FStar_Util.string_of_int n_expected
                          in
                       let uu____7777 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____7778 = FStar_Util.string_of_int n_available
                          in
                       FStar_Util.format3
                         "Expected a term with %s implicit arguments, but %s has only %s"
                         uu____7770 uu____7777 uu____7778
                        in
                     (FStar_Errors.Fatal_MissingImplicitArguments,
                       uu____7769)
                      in
                   let uu____7785 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error uu____7764 uu____7785
                 else FStar_Pervasives_Native.Some (n_available - n_expected)
              in
           let decr_inst uu___85_7807 =
             match uu___85_7807 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
              in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____7837 = FStar_Syntax_Subst.open_comp bs c  in
               (match uu____7837 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_18,uu____7949) when
                          _0_18 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____7992,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____8025 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____8025 with
                           | (v1,uu____8065,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1  in
                               let uu____8082 =
                                 aux subst2 (decr_inst inst_n) rest  in
                               (match uu____8082 with
                                | (args,bs3,subst3,g') ->
                                    let uu____8175 =
                                      FStar_TypeChecker_Rel.conj_guard g g'
                                       in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____8175)))
                      | (uu____8202,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                       in
                    let uu____8248 =
                      let uu____8275 = inst_n_binders t  in
                      aux [] uu____8275 bs1  in
                    (match uu____8248 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____8346) -> (e, torig, guard)
                          | (uu____8377,[]) when
                              let uu____8408 =
                                FStar_Syntax_Util.is_total_comp c1  in
                              Prims.op_Negation uu____8408 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____8409 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____8441 ->
                                    FStar_Syntax_Util.arrow bs2 c1
                                 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1  in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              (e1, t2, guard))))
           | uu____8456 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____8466 =
      let uu____8469 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____8469
        (FStar_List.map
           (fun u  ->
              let uu____8479 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____8479 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____8466 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____8500 = FStar_Util.set_is_empty x  in
      if uu____8500
      then []
      else
        (let s =
           let uu____8507 =
             let uu____8510 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____8510  in
           FStar_All.pipe_right uu____8507 FStar_Util.set_elements  in
         let uu____8517 =
           let uu____8518 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Gen")
              in
           if uu____8518
           then
             let uu____8519 =
               let uu____8520 = FStar_TypeChecker_Env.univ_vars env  in
               string_of_univs uu____8520  in
             FStar_Util.print1 "univ_vars in env: %s\n" uu____8519
           else ()  in
         let r =
           let uu____8527 = FStar_TypeChecker_Env.get_range env  in
           FStar_Pervasives_Native.Some uu____8527  in
         let u_names =
           FStar_All.pipe_right s
             (FStar_List.map
                (fun u  ->
                   let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                   let uu____8541 =
                     let uu____8542 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____8542
                     then
                       let uu____8543 =
                         let uu____8544 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____8544
                          in
                       let uu____8545 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____8546 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____8543 uu____8545 uu____8546
                     else ()  in
                   let uu____8548 =
                     FStar_Syntax_Unionfind.univ_change u
                       (FStar_Syntax_Syntax.U_name u_name)
                      in
                   u_name))
            in
         u_names)
  
let (gather_free_univnames :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun t  ->
      let ctx_univnames = FStar_TypeChecker_Env.univnames env  in
      let tm_univnames = FStar_Syntax_Free.univnames t  in
      let univnames1 =
        let uu____8572 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____8572 FStar_Util.set_elements  in
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
        | ([],uu____8610) -> generalized_univ_names
        | (uu____8617,[]) -> explicit_univ_names
        | uu____8624 ->
            let uu____8633 =
              let uu____8638 =
                let uu____8639 = FStar_Syntax_Print.term_to_string t  in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____8639
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____8638)
               in
            FStar_Errors.raise_error uu____8633 t.FStar_Syntax_Syntax.pos
  
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
      let uu____8656 =
        let uu____8657 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____8657
        then
          let uu____8658 = FStar_Syntax_Print.term_to_string t  in
          let uu____8659 = FStar_Syntax_Print.univ_names_to_string univnames1
             in
          FStar_Util.print2
            "generalizing universes in the term (post norm): %s with univnames: %s\n"
            uu____8658 uu____8659
        else ()  in
      let univs1 = FStar_Syntax_Free.univs t  in
      let uu____8664 =
        let uu____8665 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____8665
        then
          let uu____8666 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____8666
        else ()  in
      let gen1 = gen_univs env univs1  in
      let uu____8671 =
        let uu____8672 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____8672
        then
          let uu____8673 = FStar_Syntax_Print.term_to_string t  in
          let uu____8674 = FStar_Syntax_Print.univ_names_to_string gen1  in
          FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
            uu____8673 uu____8674
        else ()  in
      let univs2 = check_universe_generalization univnames1 gen1 t0  in
      let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t  in
      let ts = FStar_Syntax_Subst.close_univ_vars univs2 t1  in (univs2, ts)
  
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
        let uu____8750 =
          let uu____8751 =
            FStar_Util.for_all
              (fun uu____8764  ->
                 match uu____8764 with
                 | (uu____8773,uu____8774,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____8751  in
        if uu____8750
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             let uu____8820 =
               let uu____8821 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____8821
               then
                 let uu____8822 = FStar_Syntax_Print.comp_to_string c  in
                 FStar_Util.print1
                   "Normalizing before generalizing:\n\t %s\n" uu____8822
               else ()  in
             let c1 =
               FStar_TypeChecker_Normalize.normalize_comp
                 [FStar_TypeChecker_Normalize.Beta;
                 FStar_TypeChecker_Normalize.Exclude
                   FStar_TypeChecker_Normalize.Zeta;
                 FStar_TypeChecker_Normalize.NoFullNorm;
                 FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env c
                in
             let uu____8825 =
               let uu____8826 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____8826
               then
                 let uu____8827 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8827
               else ()  in
             c1  in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____8889 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____8889 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____9020 =
             match uu____9020 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress
                    in
                 let c1 = norm1 c  in
                 let t1 = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t1  in
                 let uvt = FStar_Syntax_Free.uvars t1  in
                 let uu____9085 =
                   let uu____9086 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____9086
                   then
                     let uu____9087 =
                       let uu____9088 =
                         let uu____9091 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____9091
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____9088
                         (FStar_String.concat ", ")
                        in
                     let uu____9118 =
                       let uu____9119 =
                         let uu____9122 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____9122
                           (FStar_List.map
                              (fun uu____9150  ->
                                 match uu____9150 with
                                 | (u,t2) ->
                                     let uu____9157 =
                                       FStar_Syntax_Print.uvar_to_string u
                                        in
                                     let uu____9158 =
                                       FStar_Syntax_Print.term_to_string t2
                                        in
                                     FStar_Util.format2 "(%s : %s)"
                                       uu____9157 uu____9158))
                          in
                       FStar_All.pipe_right uu____9119
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____9087
                       uu____9118
                   else ()  in
                 let univs2 =
                   let uu____9165 = FStar_Util.set_elements uvt  in
                   FStar_List.fold_left
                     (fun univs2  ->
                        fun uu____9188  ->
                          match uu____9188 with
                          | (uu____9197,t2) ->
                              let uu____9199 = FStar_Syntax_Free.univs t2  in
                              FStar_Util.set_union univs2 uu____9199) univs1
                     uu____9165
                    in
                 let uvs = gen_uvars uvt  in
                 let uu____9221 =
                   let uu____9222 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____9222
                   then
                     let uu____9223 =
                       let uu____9224 =
                         let uu____9227 = FStar_Util.set_elements univs2  in
                         FStar_All.pipe_right uu____9227
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____9224
                         (FStar_String.concat ", ")
                        in
                     let uu____9254 =
                       let uu____9255 =
                         FStar_All.pipe_right uvs
                           (FStar_List.map
                              (fun uu____9287  ->
                                 match uu____9287 with
                                 | (u,t2) ->
                                     let uu____9294 =
                                       FStar_Syntax_Print.uvar_to_string u
                                        in
                                     let uu____9295 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env t2
                                        in
                                     FStar_Util.format2 "(%s : %s)"
                                       uu____9294 uu____9295))
                          in
                       FStar_All.pipe_right uu____9255
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____9223
                       uu____9254
                   else ()  in
                 (univs2, uvs, (lbname, e, c1))
              in
           let uu____9325 =
             let uu____9358 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____9358  in
           match uu____9325 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____9479 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____9479
                 then ()
                 else
                   (let uu____9481 = lec_hd  in
                    match uu____9481 with
                    | (lb1,uu____9489,uu____9490) ->
                        let uu____9491 = lec2  in
                        (match uu____9491 with
                         | (lb2,uu____9499,uu____9500) ->
                             let msg =
                               let uu____9502 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____9503 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____9502 uu____9503
                                in
                             let uu____9504 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____9504))
                  in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun uu____9620  ->
                           match uu____9620 with
                           | (u,uu____9628) ->
                               FStar_All.pipe_right u21
                                 (FStar_Util.for_some
                                    (fun uu____9650  ->
                                       match uu____9650 with
                                       | (u',uu____9658) ->
                                           FStar_Syntax_Unionfind.equiv u u'))))
                    in
                 let uu____9663 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____9663
                 then ()
                 else
                   (let uu____9665 = lec_hd  in
                    match uu____9665 with
                    | (lb1,uu____9673,uu____9674) ->
                        let uu____9675 = lec2  in
                        (match uu____9675 with
                         | (lb2,uu____9683,uu____9684) ->
                             let msg =
                               let uu____9686 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____9687 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____9686 uu____9687
                                in
                             let uu____9688 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____9688))
                  in
               let lecs1 =
                 let uu____9698 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____9757 = univs_and_uvars_of_lec this_lec  in
                        match uu____9757 with
                        | (this_univs,this_uvs,this_lec1) ->
                            let uu____9853 =
                              force_univs_eq this_lec1 univs1 this_univs  in
                            let uu____9854 =
                              force_uvars_eq this_lec1 uvs this_uvs  in
                            this_lec1 :: lecs1) uu____9698 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____9912 = lec_hd  in
                   match uu____9912 with
                   | (lbname,e,c) ->
                       let uu____9922 =
                         let uu____9927 =
                           let uu____9928 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____9929 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____9930 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____9928 uu____9929 uu____9930
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____9927)
                          in
                       let uu____9931 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____9922 uu____9931
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun uu____9961  ->
                         match uu____9961 with
                         | (u,k) ->
                             let uu____9974 = FStar_Syntax_Unionfind.find u
                                in
                             (match uu____9974 with
                              | FStar_Pervasives_Native.Some uu____9983 ->
                                  failwith
                                    "Unexpected instantiation of mutually recursive uvar"
                              | uu____9990 ->
                                  let k1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta;
                                      FStar_TypeChecker_Normalize.Exclude
                                        FStar_TypeChecker_Normalize.Zeta] env
                                      k
                                     in
                                  let uu____9994 =
                                    FStar_Syntax_Util.arrow_formals k1  in
                                  (match uu____9994 with
                                   | (bs,kres) ->
                                       let uu____10031 =
                                         let uu____10032 =
                                           let uu____10033 =
                                             let uu____10036 =
                                               FStar_TypeChecker_Normalize.unfold_whnf
                                                 env kres
                                                in
                                             FStar_Syntax_Util.unrefine
                                               uu____10036
                                              in
                                           uu____10033.FStar_Syntax_Syntax.n
                                            in
                                         match uu____10032 with
                                         | FStar_Syntax_Syntax.Tm_type
                                             uu____10037 ->
                                             let free =
                                               FStar_Syntax_Free.names kres
                                                in
                                             let uu____10041 =
                                               let uu____10042 =
                                                 FStar_Util.set_is_empty free
                                                  in
                                               Prims.op_Negation uu____10042
                                                in
                                             if uu____10041
                                             then fail1 kres
                                             else ()
                                         | uu____10044 -> fail1 kres  in
                                       let a =
                                         let uu____10046 =
                                           let uu____10049 =
                                             FStar_TypeChecker_Env.get_range
                                               env
                                              in
                                           FStar_All.pipe_left
                                             (fun _0_19  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_19) uu____10049
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____10046 kres
                                          in
                                       let t =
                                         let uu____10053 =
                                           FStar_Syntax_Syntax.bv_to_name a
                                            in
                                         FStar_Syntax_Util.abs bs uu____10053
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 kres))
                                          in
                                       let uu____10054 =
                                         FStar_Syntax_Util.set_uvar u t  in
                                       (a,
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.imp_tag))))))
                  in
               let gen_univs1 = gen_univs env univs1  in
               let gen_tvars = gen_types uvs  in
               let ecs =
                 FStar_All.pipe_right lecs2
                   (FStar_List.map
                      (fun uu____10172  ->
                         match uu____10172 with
                         | (lbname,e,c) ->
                             let uu____10218 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____10287 ->
                                   let uu____10302 = (e, c)  in
                                   (match uu____10302 with
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
                                                (fun uu____10339  ->
                                                   match uu____10339 with
                                                   | (x,uu____10347) ->
                                                       let uu____10352 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____10352)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____10364 =
                                                let uu____10365 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____10365
                                                 in
                                              if uu____10364
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
                                          let uu____10373 =
                                            let uu____10374 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____10374.FStar_Syntax_Syntax.n
                                             in
                                          match uu____10373 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____10397 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____10397 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____10412 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____10414 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____10414, gen_tvars))
                                in
                             (match uu____10218 with
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
        let uu____10565 = let uu____10566 = Obj.magic ()  in ()  in
        let uu____10567 =
          let uu____10568 = FStar_TypeChecker_Env.debug env FStar_Options.Low
             in
          if uu____10568
          then
            let uu____10569 =
              let uu____10570 =
                FStar_List.map
                  (fun uu____10583  ->
                     match uu____10583 with
                     | (lb,uu____10591,uu____10592) ->
                         FStar_Syntax_Print.lbname_to_string lb) lecs
                 in
              FStar_All.pipe_right uu____10570 (FStar_String.concat ", ")  in
            FStar_Util.print1 "Generalizing: %s\n" uu____10569
          else ()  in
        let univnames_lecs =
          FStar_List.map
            (fun uu____10613  ->
               match uu____10613 with
               | (l,t,c) -> gather_free_univnames env t) lecs
           in
        let generalized_lecs =
          let uu____10642 = gen env is_rec lecs  in
          match uu____10642 with
          | FStar_Pervasives_Native.None  ->
              FStar_All.pipe_right lecs
                (FStar_List.map
                   (fun uu____10741  ->
                      match uu____10741 with | (l,t,c) -> (l, [], t, c, [])))
          | FStar_Pervasives_Native.Some luecs ->
              let uu____10802 =
                let uu____10803 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                if uu____10803
                then
                  FStar_All.pipe_right luecs
                    (FStar_List.iter
                       (fun uu____10847  ->
                          match uu____10847 with
                          | (l,us,e,c,gvs) ->
                              let uu____10881 =
                                FStar_Range.string_of_range
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____10882 =
                                FStar_Syntax_Print.lbname_to_string l  in
                              let uu____10883 =
                                FStar_Syntax_Print.term_to_string
                                  (FStar_Syntax_Util.comp_result c)
                                 in
                              let uu____10884 =
                                FStar_Syntax_Print.term_to_string e  in
                              let uu____10885 =
                                FStar_Syntax_Print.binders_to_string ", " gvs
                                 in
                              FStar_Util.print5
                                "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                uu____10881 uu____10882 uu____10883
                                uu____10884 uu____10885))
                else ()  in
              luecs
           in
        FStar_List.map2
          (fun univnames1  ->
             fun uu____10926  ->
               match uu____10926 with
               | (l,generalized_univs,t,c,gvs) ->
                   let uu____10970 =
                     check_universe_generalization univnames1
                       generalized_univs t
                      in
                   (l, uu____10970, t, c, gvs)) univnames_lecs
          generalized_lecs
  
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
              (let uu____11024 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____11024 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____11030 = FStar_TypeChecker_Rel.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                     uu____11030)
             in
          let is_var e1 =
            let uu____11038 =
              let uu____11039 = FStar_Syntax_Subst.compress e1  in
              uu____11039.FStar_Syntax_Syntax.n  in
            match uu____11038 with
            | FStar_Syntax_Syntax.Tm_name uu____11042 -> true
            | uu____11043 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___115_11061 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___115_11061.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___115_11061.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____11062 -> e2  in
          let env2 =
            let uu___116_11064 = env1  in
            let uu____11065 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___116_11064.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___116_11064.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___116_11064.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___116_11064.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___116_11064.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___116_11064.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___116_11064.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___116_11064.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___116_11064.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___116_11064.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___116_11064.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___116_11064.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___116_11064.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___116_11064.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___116_11064.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____11065;
              FStar_TypeChecker_Env.is_iface =
                (uu___116_11064.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___116_11064.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___116_11064.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___116_11064.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___116_11064.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___116_11064.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___116_11064.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___116_11064.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___116_11064.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___116_11064.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___116_11064.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___116_11064.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___116_11064.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___116_11064.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___116_11064.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___116_11064.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___116_11064.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___116_11064.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___116_11064.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___116_11064.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___116_11064.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____11066 = check1 env2 t1 t2  in
          match uu____11066 with
          | FStar_Pervasives_Native.None  ->
              let uu____11073 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____11078 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____11073 uu____11078
          | FStar_Pervasives_Native.Some g ->
              let uu____11084 =
                let uu____11085 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____11085
                then
                  let uu____11086 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____11086
                else ()  in
              let uu____11088 = decorate e t2  in (uu____11088, g)
  
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
          let uu____11121 = FStar_TypeChecker_Rel.force_trivial_guard env g1
             in
          FStar_Syntax_Util.is_pure_lcomp lc  in
        let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
        let uu____11123 = FStar_Syntax_Util.is_total_lcomp lc  in
        if uu____11123
        then
          let uu____11128 = discharge g1  in
          let uu____11129 = FStar_Syntax_Syntax.lcomp_comp lc  in
          (uu____11128, uu____11129)
        else
          (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
           let steps =
             [FStar_TypeChecker_Normalize.Beta;
             FStar_TypeChecker_Normalize.NoFullNorm;
             FStar_TypeChecker_Normalize.DoNotUnfoldPureLets]  in
           let c1 =
             let uu____11136 =
               let uu____11137 =
                 let uu____11138 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                 FStar_All.pipe_right uu____11138 FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____11137
                 (FStar_TypeChecker_Normalize.normalize_comp steps env)
                in
             FStar_All.pipe_right uu____11136
               (FStar_TypeChecker_Env.comp_to_comp_typ env)
              in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name
              in
           let uu____11140 = destruct_comp c1  in
           match uu____11140 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____11157 = FStar_TypeChecker_Env.get_range env  in
                 let uu____11158 =
                   let uu____11161 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial
                      in
                   let uu____11162 =
                     let uu____11163 = FStar_Syntax_Syntax.as_arg t  in
                     let uu____11164 =
                       let uu____11167 = FStar_Syntax_Syntax.as_arg wp  in
                       [uu____11167]  in
                     uu____11163 :: uu____11164  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____11161 uu____11162  in
                 uu____11158 FStar_Pervasives_Native.None uu____11157  in
               let uu____11170 =
                 let uu____11171 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification")
                    in
                 if uu____11171
                 then
                   let uu____11172 = FStar_Syntax_Print.term_to_string vc  in
                   FStar_Util.print1 "top-level VC: %s\n" uu____11172
                 else ()  in
               let g2 =
                 let uu____11175 =
                   FStar_All.pipe_left
                     FStar_TypeChecker_Rel.guard_of_guard_formula
                     (FStar_TypeChecker_Common.NonTrivial vc)
                    in
                 FStar_TypeChecker_Rel.conj_guard g1 uu____11175  in
               let uu____11176 = discharge g2  in
               let uu____11177 = FStar_Syntax_Syntax.mk_Comp c1  in
               (uu____11176, uu____11177))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___86_11208 =
        match uu___86_11208 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____11216)::[] -> f fst1
        | uu____11233 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____11239 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____11239
          (fun _0_21  -> FStar_TypeChecker_Common.NonTrivial _0_21)
         in
      let op_or_e e =
        let uu____11249 =
          let uu____11252 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____11252  in
        FStar_All.pipe_right uu____11249
          (fun _0_22  -> FStar_TypeChecker_Common.NonTrivial _0_22)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_23  -> FStar_TypeChecker_Common.NonTrivial _0_23)
         in
      let op_or_t t =
        let uu____11265 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____11265
          (fun _0_24  -> FStar_TypeChecker_Common.NonTrivial _0_24)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_25  -> FStar_TypeChecker_Common.NonTrivial _0_25)
         in
      let short_op_ite uu___87_11281 =
        match uu___87_11281 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____11289)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____11308)::[] ->
            let uu____11337 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____11337
              (fun _0_26  -> FStar_TypeChecker_Common.NonTrivial _0_26)
        | uu____11342 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____11353 =
          let uu____11361 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____11361)  in
        let uu____11368 =
          let uu____11378 =
            let uu____11386 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____11386)  in
          let uu____11393 =
            let uu____11403 =
              let uu____11411 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____11411)  in
            let uu____11418 =
              let uu____11428 =
                let uu____11436 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____11436)  in
              let uu____11443 =
                let uu____11453 =
                  let uu____11461 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____11461)  in
                [uu____11453; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____11428 :: uu____11443  in
            uu____11403 :: uu____11418  in
          uu____11378 :: uu____11393  in
        uu____11353 :: uu____11368  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____11522 =
            FStar_Util.find_map table
              (fun uu____11537  ->
                 match uu____11537 with
                 | (x,mk1) ->
                     let uu____11554 = FStar_Ident.lid_equals x lid  in
                     if uu____11554
                     then
                       let uu____11557 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____11557
                     else FStar_Pervasives_Native.None)
             in
          (match uu____11522 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____11560 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____11566 =
      let uu____11567 = FStar_Syntax_Util.un_uinst l  in
      uu____11567.FStar_Syntax_Syntax.n  in
    match uu____11566 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____11571 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____11600)::uu____11601 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____11612 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____11619,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____11620))::uu____11621 -> bs
      | uu____11638 ->
          let uu____11639 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____11639 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____11643 =
                 let uu____11644 = FStar_Syntax_Subst.compress t  in
                 uu____11644.FStar_Syntax_Syntax.n  in
               (match uu____11643 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____11648) ->
                    let uu____11665 =
                      FStar_Util.prefix_until
                        (fun uu___88_11705  ->
                           match uu___88_11705 with
                           | (uu____11712,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____11713)) ->
                               false
                           | uu____11716 -> true) bs'
                       in
                    (match uu____11665 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____11751,uu____11752) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____11824,uu____11825) ->
                         let uu____11898 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____11916  ->
                                   match uu____11916 with
                                   | (x,uu____11924) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____11898
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____11971  ->
                                     match uu____11971 with
                                     | (x,i) ->
                                         let uu____11990 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____11990, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____12000 -> bs))
  
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
            let uu____12028 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____12028
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
          let uu____12051 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____12051
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
        let uu____12081 =
          let uu____12082 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
          if uu____12082
          then
            let uu____12083 =
              let uu____12084 = FStar_Ident.text_of_lid lident  in
              d uu____12084  in
            let uu____12085 = FStar_Ident.text_of_lid lident  in
            let uu____12086 = FStar_Syntax_Print.term_to_string def  in
            FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
              uu____12085 uu____12086
          else ()  in
        let fv =
          let uu____12089 = FStar_Syntax_Util.incr_delta_qualifier def  in
          FStar_Syntax_Syntax.lid_as_fv lident uu____12089
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
        let uu____12099 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        ((let uu___117_12105 = sig_ctx  in
          {
            FStar_Syntax_Syntax.sigel =
              (uu___117_12105.FStar_Syntax_Syntax.sigel);
            FStar_Syntax_Syntax.sigrng =
              (uu___117_12105.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
            FStar_Syntax_Syntax.sigmeta =
              (uu___117_12105.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___117_12105.FStar_Syntax_Syntax.sigattrs)
          }), uu____12099)
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___89_12120 =
        match uu___89_12120 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____12121 -> false  in
      let reducibility uu___90_12126 =
        match uu___90_12126 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____12127 -> false  in
      let assumption uu___91_12132 =
        match uu___91_12132 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____12133 -> false  in
      let reification uu___92_12138 =
        match uu___92_12138 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____12139 -> true
        | uu____12140 -> false  in
      let inferred uu___93_12145 =
        match uu___93_12145 with
        | FStar_Syntax_Syntax.Discriminator uu____12146 -> true
        | FStar_Syntax_Syntax.Projector uu____12147 -> true
        | FStar_Syntax_Syntax.RecordType uu____12152 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____12161 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____12170 -> false  in
      let has_eq uu___94_12175 =
        match uu___94_12175 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____12176 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____12238 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____12243 -> true  in
      let quals = FStar_Syntax_Util.quals_of_sigelt se  in
      let uu____12247 =
        let uu____12248 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___95_12252  ->
                  match uu___95_12252 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____12253 -> false))
           in
        FStar_All.pipe_right uu____12248 Prims.op_Negation  in
      if uu____12247
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____12267 =
            let uu____12272 =
              let uu____12273 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____12273 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____12272)  in
          FStar_Errors.raise_error uu____12267 r  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____12283 = err' ""  in
        let uu____12284 =
          if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
          then err "duplicate qualifiers"
          else ()  in
        let uu____12286 =
          let uu____12287 =
            let uu____12288 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____12288  in
          if uu____12287 then err "ill-formed combination" else ()  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____12293),uu____12294) ->
            let uu____12309 =
              let uu____12310 =
                is_rec &&
                  (FStar_All.pipe_right quals
                     (FStar_List.contains
                        FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                 in
              if uu____12310
              then err "recursive definitions cannot be marked inline"
              else ()  in
            let uu____12314 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some (fun x  -> (assumption x) || (has_eq x)))
               in
            (if uu____12314
             then
               err
                 "definitions cannot be assumed or marked with equality qualifiers"
             else ())
        | FStar_Syntax_Syntax.Sig_bundle uu____12320 ->
            let uu____12329 =
              let uu____12330 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_all
                     (fun x  ->
                        (((x = FStar_Syntax_Syntax.Abstract) || (inferred x))
                           || (visibility x))
                          || (has_eq x)))
                 in
              Prims.op_Negation uu____12330  in
            (if uu____12329 then err'1 () else ())
        | FStar_Syntax_Syntax.Sig_declare_typ uu____12336 ->
            let uu____12343 =
              FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
            (if uu____12343 then err'1 () else ())
        | FStar_Syntax_Syntax.Sig_assume uu____12347 ->
            let uu____12354 =
              let uu____12355 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_all
                     (fun x  ->
                        (visibility x) ||
                          (x = FStar_Syntax_Syntax.Assumption)))
                 in
              Prims.op_Negation uu____12355  in
            (if uu____12354 then err'1 () else ())
        | FStar_Syntax_Syntax.Sig_new_effect uu____12361 ->
            let uu____12362 =
              let uu____12363 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_all
                     (fun x  ->
                        (((x = FStar_Syntax_Syntax.TotalEffect) ||
                            (inferred x))
                           || (visibility x))
                          || (reification x)))
                 in
              Prims.op_Negation uu____12363  in
            (if uu____12362 then err'1 () else ())
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12369 ->
            let uu____12370 =
              let uu____12371 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_all
                     (fun x  ->
                        (((x = FStar_Syntax_Syntax.TotalEffect) ||
                            (inferred x))
                           || (visibility x))
                          || (reification x)))
                 in
              Prims.op_Negation uu____12371  in
            (if uu____12370 then err'1 () else ())
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12377 ->
            let uu____12390 =
              let uu____12391 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_all
                     (fun x  -> (inferred x) || (visibility x)))
                 in
              Prims.op_Negation uu____12391  in
            (if uu____12390 then err'1 () else ())
        | uu____12397 -> ()
      else ()
  