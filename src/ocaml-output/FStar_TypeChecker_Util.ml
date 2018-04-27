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
  
let (new_implicit_var_aux :
  Prims.string ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.binding Prims.list ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term'
                                            FStar_Syntax_Syntax.syntax)
              FStar_Pervasives_Native.tuple2)
  =
  fun reason  ->
    fun r  ->
      fun gamma  ->
        fun binders  ->
          fun k  ->
            let ctx_uvar =
              let uu____79 = FStar_Syntax_Unionfind.fresh ()  in
              {
                FStar_Syntax_Syntax.ctx_uvar_head = uu____79;
                FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                FStar_Syntax_Syntax.ctx_uvar_typ = k;
                FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                FStar_Syntax_Syntax.ctx_uvar_should_check = true;
                FStar_Syntax_Syntax.ctx_uvar_range = r
              }  in
            FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r true
              gamma binders;
            (let uu____91 =
               FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_uvar)
                 FStar_Pervasives_Native.None r
                in
             (ctx_uvar, uu____91))
  
let (new_implicit_var :
  Prims.string ->
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.ctx_uvar,FStar_Range.range)
                                      FStar_Pervasives_Native.tuple2
                                      Prims.list,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          let uu____128 =
            FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid  in
          match uu____128 with
          | FStar_Pervasives_Native.Some (uu____151::(tm,uu____153)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                 in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____203 ->
              let binders = FStar_TypeChecker_Env.all_binders env  in
              let uu____215 =
                new_implicit_var_aux reason r env.FStar_TypeChecker_Env.gamma
                  binders k
                 in
              (match uu____215 with
               | (ctx_uvar,t) ->
                   let g =
                     let uu___98_241 = FStar_TypeChecker_Rel.trivial_guard
                        in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___98_241.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___98_241.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___98_241.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         [(reason, t, ctx_uvar, r, true)]
                     }  in
                   (t, [(ctx_uvar, r)], g))
  
let (close_guard_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun xs  ->
      fun g  ->
        let rec aux x i =
          let uu____338 = i  in
          match uu____338 with
          | (reason,term,ctx_u,range,should_check) ->
              if Prims.op_Negation should_check
              then i
              else
                (let uu____385 =
                   FStar_Syntax_Unionfind.find
                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 match uu____385 with
                 | FStar_Pervasives_Native.Some uu____400 ->
                     ((let uu____402 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____402
                       then
                         let uu____403 =
                           FStar_Syntax_Print.ctx_uvar_to_string ctx_u  in
                         FStar_Util.print1 "%s already solved; nothing to do"
                           uu____403
                       else ());
                      i)
                 | FStar_Pervasives_Native.None  ->
                     let uu____405 =
                       FStar_Util.prefix_until
                         (fun uu___79_420  ->
                            match uu___79_420 with
                            | FStar_Syntax_Syntax.Binding_var uu____421 ->
                                true
                            | uu____422 -> false)
                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma
                        in
                     (match uu____405 with
                      | FStar_Pervasives_Native.None  -> i
                      | FStar_Pervasives_Native.Some
                          (uu____445,hd1,gamma_tail) ->
                          (FStar_TypeChecker_Common.check_uvar_ctx_invariant
                             reason range should_check
                             ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma
                             ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders;
                           (match hd1 with
                            | FStar_Syntax_Syntax.Binding_var x' when
                                FStar_Syntax_Syntax.bv_eq x x' ->
                                let uu____480 =
                                  FStar_Util.prefix
                                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                   in
                                (match uu____480 with
                                 | (binders_pfx,uu____512) ->
                                     let typ =
                                       let uu____536 =
                                         let uu____543 =
                                           FStar_Syntax_Syntax.mk_binder x
                                            in
                                         [uu____543]  in
                                       let uu____556 =
                                         FStar_Syntax_Syntax.mk_Total
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                          in
                                       FStar_Syntax_Util.arrow uu____536
                                         uu____556
                                        in
                                     let uu____559 =
                                       new_implicit_var_aux reason range
                                         gamma_tail binders_pfx typ
                                        in
                                     (match uu____559 with
                                      | (ctx_v,t_v) ->
                                          let sol =
                                            let uu____587 =
                                              let uu____592 =
                                                let uu____593 =
                                                  let uu____600 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      x
                                                     in
                                                  FStar_Syntax_Syntax.as_arg
                                                    uu____600
                                                   in
                                                [uu____593]  in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                t_v uu____592
                                               in
                                            uu____587
                                              FStar_Pervasives_Native.None
                                              range
                                             in
                                          ((let uu____616 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env)
                                                (FStar_Options.Other "Rel")
                                               in
                                            if uu____616
                                            then
                                              let uu____617 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              let uu____618 =
                                                FStar_Syntax_Print.ctx_uvar_to_string
                                                  ctx_u
                                                 in
                                              let uu____619 =
                                                FStar_Syntax_Print.term_to_string
                                                  sol
                                                 in
                                              FStar_Util.print3
                                                "Closing implicit %s with binder %s to %s\n"
                                                uu____617 uu____618 uu____619
                                            else ());
                                           FStar_Syntax_Unionfind.change
                                             ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                             sol;
                                           (reason, t_v, ctx_v, range,
                                             should_check))))
                            | uu____624 -> i))))
           in
        let uu____625 =
          FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred
            (FStar_List.partition
               (fun uu____671  ->
                  match uu____671 with
                  | (uu____676,p) ->
                      FStar_TypeChecker_Rel.flex_prob_closing env xs p))
           in
        match uu____625 with
        | (solve_now,defer) ->
            let g1 =
              FStar_TypeChecker_Rel.solve_deferred_constraints env
                (let uu___99_706 = g  in
                 {
                   FStar_TypeChecker_Env.guard_f =
                     (uu___99_706.FStar_TypeChecker_Env.guard_f);
                   FStar_TypeChecker_Env.deferred = solve_now;
                   FStar_TypeChecker_Env.univ_ineqs =
                     (uu___99_706.FStar_TypeChecker_Env.univ_ineqs);
                   FStar_TypeChecker_Env.implicits =
                     (uu___99_706.FStar_TypeChecker_Env.implicits)
                 })
               in
            let g2 =
              let uu___100_708 = g1  in
              {
                FStar_TypeChecker_Env.guard_f =
                  (uu___100_708.FStar_TypeChecker_Env.guard_f);
                FStar_TypeChecker_Env.deferred = defer;
                FStar_TypeChecker_Env.univ_ineqs =
                  (uu___100_708.FStar_TypeChecker_Env.univ_ineqs);
                FStar_TypeChecker_Env.implicits =
                  (uu___100_708.FStar_TypeChecker_Env.implicits)
              }  in
            ((let uu____710 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____710
              then
                let uu____711 = FStar_Syntax_Print.binders_to_string ", " xs
                   in
                FStar_Util.print1
                  "Starting to close implicits with binders {%s}\n" uu____711
              else ());
             (let is =
                FStar_List.fold_right
                  (fun uu____751  ->
                     fun is  ->
                       match uu____751 with
                       | (x,uu____786) ->
                           ((let uu____788 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____788
                             then
                               let uu____789 =
                                 FStar_Syntax_Print.bv_to_string x  in
                               FStar_Util.print1 "Considering closing %s\n"
                                 uu____789
                             else ());
                            FStar_List.map (aux x) is)) xs
                  g2.FStar_TypeChecker_Env.implicits
                 in
              let g3 =
                let uu___101_816 = g2  in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___101_816.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___101_816.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___101_816.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = is
                }  in
              (let uu____818 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____818
               then
                 let uu____819 = FStar_Syntax_Print.binders_to_string ", " xs
                    in
                 let uu____820 = FStar_TypeChecker_Rel.guard_to_string env g3
                    in
                 FStar_Util.print2
                   "Closed implicits with binders {%s}; guard is\n\t%s\n"
                   uu____819 uu____820
               else ());
              g3))
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____835 =
        let uu____836 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____836  in
      if uu____835
      then
        let us =
          let uu____838 =
            let uu____841 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____841
             in
          FStar_All.pipe_right uu____838 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____852 =
            let uu____857 =
              let uu____858 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____858
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____857)  in
          FStar_Errors.log_issue r uu____852);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.typ,Prims.bool)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun uu____875  ->
      match uu____875 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____885;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____887;
          FStar_Syntax_Syntax.lbpos = uu____888;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____921 = FStar_Syntax_Subst.open_univ_vars univ_vars1 e
                  in
               (match uu____921 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____958) -> aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____965) ->
                          FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1020) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____1052 = FStar_Options.ml_ish ()  in
                                if uu____1052
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____1069 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____1069
                            then
                              let uu____1070 = FStar_Range.string_of_range r
                                 in
                              let uu____1071 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____1070 uu____1071
                            else ());
                           FStar_Util.Inl t2)
                      | uu____1073 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____1075 = aux e1  in
                      match uu____1075 with
                      | FStar_Util.Inr c ->
                          let uu____1081 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____1081
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____1083 =
                               let uu____1088 =
                                 let uu____1089 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____1089
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____1088)
                                in
                             FStar_Errors.raise_error uu____1083 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars2, t2, true))
           | uu____1093 ->
               let uu____1094 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____1094 with
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
            let uu____1188 =
              let uu____1193 =
                FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
              match uu____1193 with
              | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____1198;
                  FStar_Syntax_Syntax.vars = uu____1199;_} ->
                  let uu____1202 = FStar_Syntax_Util.type_u ()  in
                  (match uu____1202 with
                   | (t,uu____1212) ->
                       let uu____1213 =
                         let uu____1226 = FStar_Syntax_Syntax.range_of_bv x
                            in
                         new_implicit_var "" uu____1226 env1 t  in
                       (match uu____1213 with | (t1,uu____1232,g) -> (t1, g)))
              | t -> tc_annot env1 t  in
            match uu____1188 with
            | (t_x,guard) ->
                ((let uu___102_1254 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___102_1254.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___102_1254.FStar_Syntax_Syntax.index);
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
                  | uu____1329 ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant c)
                        FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                   in
                ([], [], [], env1, e, FStar_TypeChecker_Rel.trivial_guard,
                  p1)
            | FStar_Syntax_Syntax.Pat_dot_term (x,uu____1337) ->
                let uu____1342 = FStar_Syntax_Util.type_u ()  in
                (match uu____1342 with
                 | (k,uu____1368) ->
                     let uu____1369 =
                       let uu____1382 = FStar_Syntax_Syntax.range_of_bv x  in
                       new_implicit_var "" uu____1382 env1 k  in
                     (match uu____1369 with
                      | (t,uu____1404,g) ->
                          let x1 =
                            let uu___103_1419 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___103_1419.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___103_1419.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t
                            }  in
                          let uu____1420 =
                            let uu____1433 =
                              FStar_Syntax_Syntax.range_of_bv x1  in
                            new_implicit_var "" uu____1433 env1 t  in
                          (match uu____1420 with
                           | (e,uu____1455,g') ->
                               let p2 =
                                 let uu___104_1472 = p1  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_dot_term
                                        (x1, e));
                                   FStar_Syntax_Syntax.p =
                                     (uu___104_1472.FStar_Syntax_Syntax.p)
                                 }  in
                               let uu____1475 =
                                 FStar_TypeChecker_Rel.conj_guard g g'  in
                               ([], [], [], env1, e, uu____1475, p2))))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let uu____1483 = check_bv env1 x  in
                (match uu____1483 with
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
                let uu____1522 = check_bv env1 x  in
                (match uu____1522 with
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
                let uu____1577 =
                  FStar_All.pipe_right pats
                    (FStar_List.fold_left
                       (fun uu____1723  ->
                          fun uu____1724  ->
                            match (uu____1723, uu____1724) with
                            | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                                let uu____1922 =
                                  pat_as_arg_with_env allow_wc_dependence
                                    env2 p2
                                   in
                                (match uu____1922 with
                                 | (b',a',w',env3,te,guard',pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te  in
                                     let uu____1998 =
                                       FStar_TypeChecker_Rel.conj_guard guard
                                         guard'
                                        in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), uu____1998, ((pat, imp)
                                       :: pats1))))
                       ([], [], [], env1, [],
                         FStar_TypeChecker_Rel.trivial_guard, []))
                   in
                (match uu____1577 with
                 | (b,a,w,env2,args,guard,pats1) ->
                     let e =
                       let uu____2141 =
                         let uu____2146 = FStar_Syntax_Syntax.fv_to_tm fv  in
                         let uu____2147 =
                           FStar_All.pipe_right args FStar_List.rev  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2146 uu____2147
                          in
                       uu____2141 FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     let uu____2164 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten
                        in
                     let uu____2175 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten
                        in
                     let uu____2186 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten
                        in
                     (uu____2164, uu____2175, uu____2186, env2, e, guard,
                       (let uu___105_2204 = p1  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___105_2204.FStar_Syntax_Syntax.p)
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
                    (fun uu____2304  ->
                       match uu____2304 with
                       | (p2,imp) ->
                           let uu____2323 = elaborate_pat env1 p2  in
                           (uu____2323, imp)) pats
                   in
                let uu____2328 =
                  FStar_TypeChecker_Env.lookup_datacon env1
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____2328 with
                 | (uu____2335,t) ->
                     let uu____2337 = FStar_Syntax_Util.arrow_formals t  in
                     (match uu____2337 with
                      | (f,uu____2353) ->
                          let rec aux formals pats2 =
                            match (formals, pats2) with
                            | ([],[]) -> []
                            | ([],uu____2479::uu____2480) ->
                                let uu____2523 =
                                  FStar_Ident.range_of_lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_TooManyPatternArguments,
                                    "Too many pattern arguments") uu____2523
                            | (uu____2532::uu____2533,[]) ->
                                FStar_All.pipe_right formals
                                  (FStar_List.map
                                     (fun uu____2611  ->
                                        match uu____2611 with
                                        | (t1,imp) ->
                                            (match imp with
                                             | FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Syntax.Implicit
                                                 inaccessible) ->
                                                 let a =
                                                   let uu____2638 =
                                                     let uu____2641 =
                                                       FStar_Syntax_Syntax.range_of_bv
                                                         t1
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____2641
                                                      in
                                                   FStar_Syntax_Syntax.new_bv
                                                     uu____2638
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let r =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 let uu____2643 =
                                                   maybe_dot inaccessible a r
                                                    in
                                                 (uu____2643, true)
                                             | uu____2648 ->
                                                 let uu____2651 =
                                                   let uu____2656 =
                                                     let uu____2657 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1
                                                        in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____2657
                                                      in
                                                   (FStar_Errors.Fatal_InsufficientPatternArguments,
                                                     uu____2656)
                                                    in
                                                 let uu____2658 =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____2651 uu____2658)))
                            | (f1::formals',(p2,p_imp)::pats') ->
                                (match f1 with
                                 | (uu____2732,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    uu____2733)) when p_imp ->
                                     let uu____2736 = aux formals' pats'  in
                                     (p2, true) :: uu____2736
                                 | (uu____2753,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    inaccessible)) ->
                                     let a =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p2.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     let p3 =
                                       let uu____2761 =
                                         FStar_Ident.range_of_lid
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          in
                                       maybe_dot inaccessible a uu____2761
                                        in
                                     let uu____2762 = aux formals' pats2  in
                                     (p3, true) :: uu____2762
                                 | (uu____2779,imp) ->
                                     let uu____2785 =
                                       let uu____2792 =
                                         FStar_Syntax_Syntax.is_implicit imp
                                          in
                                       (p2, uu____2792)  in
                                     let uu____2795 = aux formals' pats'  in
                                     uu____2785 :: uu____2795)
                             in
                          let uu___106_2810 = p1  in
                          let uu____2813 =
                            let uu____2814 =
                              let uu____2827 = aux f pats1  in
                              (fv, uu____2827)  in
                            FStar_Syntax_Syntax.Pat_cons uu____2814  in
                          {
                            FStar_Syntax_Syntax.v = uu____2813;
                            FStar_Syntax_Syntax.p =
                              (uu___106_2810.FStar_Syntax_Syntax.p)
                          }))
            | uu____2844 -> p1  in
          let one_pat allow_wc_dependence env1 p1 =
            let p2 = elaborate_pat env1 p1  in
            let uu____2886 = pat_as_arg_with_env allow_wc_dependence env1 p2
               in
            match uu____2886 with
            | (b,a,w,env2,arg,guard,p3) ->
                let uu____2944 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                   in
                (match uu____2944 with
                 | FStar_Pervasives_Native.Some x ->
                     let uu____2970 =
                       FStar_TypeChecker_Err.nonlinear_pattern_variable x  in
                     FStar_Errors.raise_error uu____2970
                       p3.FStar_Syntax_Syntax.p
                 | uu____2993 -> (b, a, w, arg, guard, p3))
             in
          let uu____3002 = one_pat true env p  in
          match uu____3002 with
          | (b,uu____3032,uu____3033,tm,guard,p1) -> (b, tm, guard, p1)
  
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
          | (uu____3095,FStar_Syntax_Syntax.Tm_uinst (e2,uu____3097)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____3102,uu____3103) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____3107 =
                    let uu____3108 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____3109 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____3108 uu____3109
                     in
                  failwith uu____3107)
               else ();
               (let uu____3112 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat")
                   in
                if uu____3112
                then
                  let uu____3113 = FStar_Syntax_Print.bv_to_string x  in
                  let uu____3114 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____3113
                    uu____3114
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___107_3118 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___107_3118.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___107_3118.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____3122 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation
                   in
                if uu____3122
                then
                  let uu____3123 =
                    let uu____3124 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____3125 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____3124 uu____3125
                     in
                  failwith uu____3123
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___108_3129 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___108_3129.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___108_3129.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____3131),uu____3132) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____3156 =
                  let uu____3157 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  Prims.op_Negation uu____3157  in
                if uu____3156
                then
                  let uu____3158 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3158
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____3177;
                FStar_Syntax_Syntax.vars = uu____3178;_},args))
              ->
              ((let uu____3217 =
                  let uu____3218 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____3218 Prims.op_Negation  in
                if uu____3217
                then
                  let uu____3219 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3219
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3357)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3432) ->
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
                       | ((e2,imp),uu____3469) ->
                           let pat =
                             let uu____3491 = aux argpat e2  in
                             let uu____3492 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3491, uu____3492)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3497 ->
                      let uu____3520 =
                        let uu____3521 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3522 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3521 uu____3522
                         in
                      failwith uu____3520
                   in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____3532;
                     FStar_Syntax_Syntax.vars = uu____3533;_},uu____3534);
                FStar_Syntax_Syntax.pos = uu____3535;
                FStar_Syntax_Syntax.vars = uu____3536;_},args))
              ->
              ((let uu____3579 =
                  let uu____3580 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____3580 Prims.op_Negation  in
                if uu____3579
                then
                  let uu____3581 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3581
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3719)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3794) ->
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
                       | ((e2,imp),uu____3831) ->
                           let pat =
                             let uu____3853 = aux argpat e2  in
                             let uu____3854 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3853, uu____3854)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3859 ->
                      let uu____3882 =
                        let uu____3883 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3884 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3883 uu____3884
                         in
                      failwith uu____3882
                   in
                match_args [] args argpats))
          | uu____3891 ->
              let uu____3896 =
                let uu____3897 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p  in
                let uu____3898 = FStar_Syntax_Print.pat_to_string qq  in
                let uu____3899 = FStar_Syntax_Print.term_to_string exp  in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____3897 uu____3898 uu____3899
                 in
              failwith uu____3896
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
    let pat_as_arg uu____3942 =
      match uu____3942 with
      | (p,i) ->
          let uu____3959 = decorated_pattern_as_term p  in
          (match uu____3959 with
           | (vars,te) ->
               let uu____3982 =
                 let uu____3987 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____3987)  in
               (vars, uu____3982))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____4001 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____4001)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____4005 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____4005)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____4009 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____4009)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____4030 =
          let uu____4047 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____4047 FStar_List.unzip  in
        (match uu____4030 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____4169 =
               let uu____4170 =
                 let uu____4171 =
                   let uu____4186 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____4186, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____4171  in
               mk1 uu____4170  in
             (vars1, uu____4169))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____4222,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____4232,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____4246 -> FStar_Pervasives_Native.Some hd1)
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____4268)::[] -> wp
      | uu____4285 ->
          let uu____4294 =
            let uu____4295 =
              let uu____4296 =
                FStar_List.map
                  (fun uu____4306  ->
                     match uu____4306 with
                     | (x,uu____4312) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____4296 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____4295
             in
          failwith uu____4294
       in
    let uu____4315 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____4315, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____4331 = destruct_comp c  in
        match uu____4331 with
        | (u,uu____4339,wp) ->
            let uu____4341 =
              let uu____4350 =
                let uu____4357 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____4357  in
              [uu____4350]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____4341;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____4385 =
          let uu____4392 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____4393 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____4392 uu____4393  in
        match uu____4385 with | (m,uu____4395,uu____4396) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____4412 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____4412
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
        let uu____4455 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____4455 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____4492 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____4492 with
             | (a,kwp) ->
                 let uu____4523 = destruct_comp m1  in
                 let uu____4530 = destruct_comp m2  in
                 ((md, a, kwp), uu____4523, uu____4530))
  
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
            let uu____4610 =
              let uu____4611 =
                let uu____4620 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____4620]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4611;
                FStar_Syntax_Syntax.flags = flags1
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4610
  
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
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun flags1  ->
          let uu____4696 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____4696
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
      let uu____4708 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____4708
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____4711  ->
           let uu____4712 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____4712)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4718 =
      let uu____4719 = FStar_Syntax_Subst.compress t  in
      uu____4719.FStar_Syntax_Syntax.n  in
    match uu____4718 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4722 -> true
    | uu____4735 -> false
  
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
              let uu____4792 =
                let uu____4793 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____4793  in
              if uu____4792
              then f
              else (let uu____4795 = reason1 ()  in label uu____4795 r f)
  
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
            let uu___109_4812 = g  in
            let uu____4813 =
              let uu____4814 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____4814  in
            {
              FStar_TypeChecker_Env.guard_f = uu____4813;
              FStar_TypeChecker_Env.deferred =
                (uu___109_4812.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___109_4812.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___109_4812.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4834 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4834
        then c
        else
          (let uu____4836 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____4836
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4895 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____4895]  in
                       let us =
                         let uu____4911 =
                           let uu____4914 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____4914]  in
                         u_res :: uu____4911  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____4920 =
                         let uu____4925 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____4926 =
                           let uu____4927 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____4934 =
                             let uu____4943 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____4950 =
                               let uu____4959 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____4959]  in
                             uu____4943 :: uu____4950  in
                           uu____4927 :: uu____4934  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4925 uu____4926
                          in
                       uu____4920 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____4993 = destruct_comp c1  in
              match uu____4993 with
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
          (fun uu____5028  ->
             let uu____5029 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____5029)
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___80_5038  ->
            match uu___80_5038 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____5039 -> false))
  
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
                (let uu____5061 =
                   FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ
                    in
                 Prims.op_Negation uu____5061))
               &&
               (let uu____5068 = FStar_Syntax_Util.head_and_args' e  in
                match uu____5068 with
                | (head1,uu____5082) ->
                    let uu____5099 =
                      let uu____5100 = FStar_Syntax_Util.un_uinst head1  in
                      uu____5100.FStar_Syntax_Syntax.n  in
                    (match uu____5099 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____5104 =
                           let uu____5105 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____5105
                            in
                         Prims.op_Negation uu____5104
                     | uu____5106 -> true)))
              &&
              (let uu____5108 = should_not_inline_lc lc  in
               Prims.op_Negation uu____5108)
  
let (return_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun u_t_opt  ->
      fun t  ->
        fun v1  ->
          let c =
            let uu____5142 =
              let uu____5143 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____5143  in
            if uu____5142
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____5145 = FStar_Syntax_Util.is_unit t  in
               if uu____5145
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
                    let uu____5151 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____5151
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____5153 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____5153 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____5163 =
                             let uu____5164 =
                               let uu____5169 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____5170 =
                                 let uu____5171 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____5178 =
                                   let uu____5187 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____5187]  in
                                 uu____5171 :: uu____5178  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____5169
                                 uu____5170
                                in
                             uu____5164 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.NoFullNorm] env
                             uu____5163)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____5215 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____5215
           then
             let uu____5216 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____5217 = FStar_Syntax_Print.term_to_string v1  in
             let uu____5218 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____5216 uu____5217 uu____5218
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    let uu____5231 =
      FStar_All.pipe_right flags1
        (FStar_Util.for_some
           (fun uu___81_5235  ->
              match uu___81_5235 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5236 -> false))
       in
    if uu____5231
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags1
        (FStar_List.collect
           (fun uu___82_5245  ->
              match uu___82_5245 with
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
        let uu____5264 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5264
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____5267 = destruct_comp c1  in
           match uu____5267 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____5281 =
                   let uu____5286 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____5287 =
                     let uu____5288 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____5295 =
                       let uu____5304 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____5311 =
                         let uu____5320 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____5320]  in
                       uu____5304 :: uu____5311  in
                     uu____5288 :: uu____5295  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____5286 uu____5287  in
                 uu____5281 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____5353 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t wp1 uu____5353)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5376 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____5378 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____5378
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____5381 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____5381 weaken
  
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
               let uu____5424 = destruct_comp c1  in
               match uu____5424 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____5438 =
                       let uu____5443 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____5444 =
                         let uu____5445 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____5452 =
                           let uu____5461 =
                             let uu____5468 =
                               let uu____5469 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____5469 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____5468
                              in
                           let uu____5476 =
                             let uu____5485 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____5485]  in
                           uu____5461 :: uu____5476  in
                         uu____5445 :: uu____5452  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5443 uu____5444
                        in
                     uu____5438 FStar_Pervasives_Native.None
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
            let uu____5560 = FStar_TypeChecker_Rel.is_trivial g0  in
            if uu____5560
            then (lc, g0)
            else
              (let flags1 =
                 let uu____5569 =
                   let uu____5576 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____5576
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5569 with
                 | (maybe_trivial_post,flags1) ->
                     let uu____5596 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___83_5604  ->
                               match uu___83_5604 with
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
                               | uu____5607 -> []))
                        in
                     FStar_List.append flags1 uu____5596
                  in
               let strengthen uu____5613 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____5617 = FStar_TypeChecker_Rel.guard_form g01  in
                    match uu____5617 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____5620 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____5620
                          then
                            let uu____5621 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debug_only
                               in
                            let uu____5622 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____5621 uu____5622
                          else ());
                         strengthen_comp env reason c f flags1))
                  in
               let uu____5624 =
                 let uu____5625 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____5625
                   lc.FStar_Syntax_Syntax.res_typ flags1 strengthen
                  in
               (uu____5624,
                 (let uu___110_5627 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___110_5627.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___110_5627.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___110_5627.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___84_5634  ->
            match uu___84_5634 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____5635 -> false) lc.FStar_Syntax_Syntax.cflags)
  
let (maybe_add_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun uopt  ->
      fun lc  ->
        fun e  ->
          let uu____5662 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____5662
          then e
          else
            (let uu____5666 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____5668 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____5668)
                in
             if uu____5666
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
          fun uu____5718  ->
            match uu____5718 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____5738 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____5738 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____5746 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____5746
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags1 =
                       let uu____5753 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____5753
                       then
                         let uu____5756 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____5756
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5760 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____5760
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5765 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____5765
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____5769 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____5769
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags1
                     else flags1)
                   in
                let bind_it uu____5778 =
                  let uu____5779 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____5779
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
                       (fun uu____5793  ->
                          let uu____5794 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____5795 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____5797 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____5794 uu____5795 uu____5797);
                     (let aux uu____5811 =
                        let uu____5812 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____5812
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____5833 ->
                              let uu____5834 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____5834
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____5853 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____5853
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let subst_c2 e1opt1 reason =
                        match (e1opt1, b) with
                        | (FStar_Pervasives_Native.Some
                           e,FStar_Pervasives_Native.Some x) ->
                            let uu____5924 =
                              let uu____5929 =
                                FStar_Syntax_Subst.subst_comp
                                  [FStar_Syntax_Syntax.NT (x, e)] c2
                                 in
                              (uu____5929, reason)  in
                            FStar_Util.Inl uu____5924
                        | uu____5936 -> aux ()  in
                      let try_simplify uu____5960 =
                        let rec maybe_close t x c =
                          let uu____5977 =
                            let uu____5978 =
                              FStar_TypeChecker_Normalize.unfold_whnf env t
                               in
                            uu____5978.FStar_Syntax_Syntax.n  in
                          match uu____5977 with
                          | FStar_Syntax_Syntax.Tm_refine (y,uu____5982) ->
                              maybe_close y.FStar_Syntax_Syntax.sort x c
                          | FStar_Syntax_Syntax.Tm_fvar fv when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.unit_lid
                              -> close_comp env [x] c
                          | uu____5988 -> c  in
                        let uu____5989 =
                          let uu____5990 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____5990  in
                        if uu____5989
                        then
                          let uu____6001 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____6001
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____6015 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____6015))
                        else
                          (let uu____6025 =
                             (FStar_Syntax_Util.is_total_comp c1) &&
                               (FStar_Syntax_Util.is_total_comp c2)
                              in
                           if uu____6025
                           then subst_c2 e1opt "both total"
                           else
                             (let uu____6035 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____6035
                              then
                                let uu____6044 =
                                  let uu____6049 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____6049, "both gtot")  in
                                FStar_Util.Inl uu____6044
                              else
                                (match (e1opt, b) with
                                 | (FStar_Pervasives_Native.Some
                                    e,FStar_Pervasives_Native.Some x) ->
                                     let uu____6073 =
                                       (FStar_Syntax_Util.is_total_comp c1)
                                         &&
                                         (let uu____6075 =
                                            FStar_Syntax_Syntax.is_null_bv x
                                             in
                                          Prims.op_Negation uu____6075)
                                        in
                                     if uu____6073
                                     then
                                       let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e)] c2
                                          in
                                       let x1 =
                                         let uu___111_6088 = x  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___111_6088.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___111_6088.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             (FStar_Syntax_Util.comp_result
                                                c1)
                                         }  in
                                       let uu____6089 =
                                         let uu____6094 =
                                           maybe_close
                                             x1.FStar_Syntax_Syntax.sort x1
                                             c21
                                            in
                                         (uu____6094, "c1 Tot")  in
                                       FStar_Util.Inl uu____6089
                                     else aux ()
                                 | uu____6100 -> aux ())))
                         in
                      let uu____6109 = try_simplify ()  in
                      match uu____6109 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____6129  ->
                                let uu____6130 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____6130);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____6139  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____6160 = lift_and_destruct env c11 c21
                                 in
                              match uu____6160 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____6213 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____6213]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____6227 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____6227]
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
                                    let uu____6254 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____6261 =
                                      let uu____6270 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____6277 =
                                        let uu____6286 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____6293 =
                                          let uu____6302 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____6309 =
                                            let uu____6318 =
                                              let uu____6325 = mk_lam wp2  in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____6325
                                               in
                                            [uu____6318]  in
                                          uu____6302 :: uu____6309  in
                                        uu____6286 :: uu____6293  in
                                      uu____6270 :: uu____6277  in
                                    uu____6254 :: uu____6261  in
                                  let wp =
                                    let uu____6365 =
                                      let uu____6370 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____6370 wp_args
                                       in
                                    uu____6365 FStar_Pervasives_Native.None
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
                              let uu____6395 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____6395 with
                              | (m,uu____6403,lift2) ->
                                  let c23 =
                                    let uu____6406 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____6406
                                     in
                                  let uu____6407 = destruct_comp c12  in
                                  (match uu____6407 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____6421 =
                                           let uu____6426 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____6427 =
                                             let uu____6428 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____6435 =
                                               let uu____6444 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____6444]  in
                                             uu____6428 :: uu____6435  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6426 uu____6427
                                            in
                                         uu____6421
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
                            let uu____6475 = destruct_comp c1_typ  in
                            match uu____6475 with
                            | (u_res_t1,res_t1,uu____6484) ->
                                let uu____6485 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____6485
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____6488 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____6488
                                   then
                                     (debug1
                                        (fun uu____6496  ->
                                           let uu____6497 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____6498 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____6497 uu____6498);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____6503 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____6505 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____6505)
                                         in
                                      if uu____6503
                                      then
                                        let e1' =
                                          let uu____6525 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____6525
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____6534  ->
                                              let uu____6535 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____6536 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____6535 uu____6536);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____6548  ->
                                              let uu____6549 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____6550 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____6549 uu____6550);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____6555 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____6555
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
      | uu____6571 -> g2
  
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
            (let uu____6593 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____6593)
           in
        let flags1 =
          if should_return1
          then
            let uu____6599 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____6599
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____6611 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____6615 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____6615
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____6619 =
              let uu____6620 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____6620  in
            (if uu____6619
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___112_6625 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___112_6625.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___112_6625.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___112_6625.FStar_Syntax_Syntax.effect_args);
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
               let uu____6636 =
                 let uu____6637 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____6637
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6636
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____6640 =
               let uu____6641 =
                 let uu____6642 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____6642
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____6641  in
             FStar_Syntax_Util.comp_set_flags uu____6640 flags1)
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
            fun uu____6677  ->
              match uu____6677 with
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
                    let uu____6689 =
                      ((let uu____6692 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____6692) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____6689
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6706 =
        let uu____6707 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6707  in
      FStar_Syntax_Syntax.fvar uu____6706 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____6773  ->
                 match uu____6773 with
                 | (uu____6786,eff_label,uu____6788,uu____6789) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____6800 =
          let uu____6807 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____6841  ->
                    match uu____6841 with
                    | (uu____6854,uu____6855,flags1,uu____6857) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___85_6871  ->
                                match uu___85_6871 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____6872 -> false))))
             in
          if uu____6807
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____6800 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____6895 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____6897 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____6897
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____6935 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____6936 =
                     let uu____6941 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____6942 =
                       let uu____6943 = FStar_Syntax_Syntax.as_arg res_t1  in
                       let uu____6950 =
                         let uu____6959 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____6966 =
                           let uu____6975 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____6982 =
                             let uu____6991 = FStar_Syntax_Syntax.as_arg wp_e
                                in
                             [uu____6991]  in
                           uu____6975 :: uu____6982  in
                         uu____6959 :: uu____6966  in
                       uu____6943 :: uu____6950  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____6941 uu____6942  in
                   uu____6936 FStar_Pervasives_Native.None uu____6935  in
                 let default_case =
                   let post_k =
                     let uu____7034 =
                       let uu____7041 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____7041]  in
                     let uu____7054 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7034 uu____7054  in
                   let kwp =
                     let uu____7060 =
                       let uu____7067 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____7067]  in
                     let uu____7080 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7060 uu____7080  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____7087 =
                       let uu____7088 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____7088]  in
                     let uu____7101 =
                       let uu____7104 =
                         let uu____7111 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____7111
                          in
                       let uu____7112 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____7104 uu____7112  in
                     FStar_Syntax_Util.abs uu____7087 uu____7101
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
                   let uu____7134 =
                     should_not_inline_whole_match ||
                       (let uu____7136 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____7136)
                      in
                   if uu____7134 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____7169  ->
                        fun celse  ->
                          match uu____7169 with
                          | (g,eff_label,uu____7185,cthen) ->
                              let uu____7197 =
                                let uu____7222 =
                                  let uu____7223 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____7223
                                   in
                                lift_and_destruct env uu____7222 celse  in
                              (match uu____7197 with
                               | ((md,uu____7225,uu____7226),(uu____7227,uu____7228,wp_then),
                                  (uu____7230,uu____7231,wp_else)) ->
                                   let uu____7251 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____7251 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____7265::[] -> comp
                 | uu____7305 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____7323 = destruct_comp comp1  in
                     (match uu____7323 with
                      | (uu____7330,uu____7331,wp) ->
                          let wp1 =
                            let uu____7336 =
                              let uu____7341 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____7342 =
                                let uu____7343 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____7350 =
                                  let uu____7359 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____7359]  in
                                uu____7343 :: uu____7350  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____7341
                                uu____7342
                               in
                            uu____7336 FStar_Pervasives_Native.None
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
          let uu____7418 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____7418 with
          | FStar_Pervasives_Native.None  ->
              let uu____7427 =
                FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                  env e c c'
                 in
              let uu____7432 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____7427 uu____7432
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
            let uu____7475 =
              let uu____7476 = FStar_Syntax_Subst.compress t2  in
              uu____7476.FStar_Syntax_Syntax.n  in
            match uu____7475 with
            | FStar_Syntax_Syntax.Tm_type uu____7479 -> true
            | uu____7480 -> false  in
          let uu____7481 =
            let uu____7482 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ  in
            uu____7482.FStar_Syntax_Syntax.n  in
          match uu____7481 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____7490 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid
                 in
              let b2t1 =
                let uu____7500 =
                  FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                    e.FStar_Syntax_Syntax.pos
                   in
                FStar_Syntax_Syntax.fvar uu____7500
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None
                 in
              let lc1 =
                let uu____7502 =
                  let uu____7503 =
                    let uu____7504 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____7504
                     in
                  (FStar_Pervasives_Native.None, uu____7503)  in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____7502
                 in
              let e1 =
                let uu____7510 =
                  let uu____7515 =
                    let uu____7516 = FStar_Syntax_Syntax.as_arg e  in
                    [uu____7516]  in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____7515  in
                uu____7510 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos
                 in
              (e1, lc1)
          | uu____7537 -> (e, lc)
  
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
              (let uu____7574 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name
                  in
               match uu____7574 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____7597 -> false)
             in
          let gopt =
            if use_eq
            then
              let uu____7619 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t
                 in
              (uu____7619, false)
            else
              (let uu____7625 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____7625, true))
             in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____7636) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____7645 =
                  FStar_TypeChecker_Err.basic_type_error env
                    (FStar_Pervasives_Native.Some e) t
                    lc.FStar_Syntax_Syntax.res_typ
                   in
                FStar_Errors.raise_error uu____7645 e.FStar_Syntax_Syntax.pos
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___113_7659 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___113_7659.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___113_7659.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___113_7659.FStar_Syntax_Syntax.comp_thunk)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____7664 = FStar_TypeChecker_Rel.guard_form g  in
              (match uu____7664 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___114_7672 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___114_7672.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___114_7672.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___114_7672.FStar_Syntax_Syntax.comp_thunk)
                     }  in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___115_7675 = g  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___115_7675.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___115_7675.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___115_7675.FStar_TypeChecker_Env.implicits)
                     }  in
                   let strengthen uu____7681 =
                     let uu____7682 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ())
                        in
                     if uu____7682
                     then FStar_Syntax_Syntax.lcomp_comp lc
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f
                           in
                        let uu____7685 =
                          let uu____7686 = FStar_Syntax_Subst.compress f1  in
                          uu____7686.FStar_Syntax_Syntax.n  in
                        match uu____7685 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____7689,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____7691;
                                          FStar_Syntax_Syntax.vars =
                                            uu____7692;_},uu____7693)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___116_7715 = lc  in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___116_7715.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___116_7715.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp_thunk =
                                  (uu___116_7715.FStar_Syntax_Syntax.comp_thunk)
                              }  in
                            FStar_Syntax_Syntax.lcomp_comp lc1
                        | uu____7716 ->
                            let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                            ((let uu____7719 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____7719
                              then
                                let uu____7720 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____7721 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t
                                   in
                                let uu____7722 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c
                                   in
                                let uu____7723 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1
                                   in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____7720 uu____7721 uu____7722 uu____7723
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
                                  let uu____7732 =
                                    let uu____7737 =
                                      let uu____7738 =
                                        FStar_Syntax_Syntax.as_arg xexp  in
                                      [uu____7738]  in
                                    FStar_Syntax_Syntax.mk_Tm_app f1
                                      uu____7737
                                     in
                                  uu____7732 FStar_Pervasives_Native.None
                                    f1.FStar_Syntax_Syntax.pos
                                else f1  in
                              let uu____7760 =
                                let uu____7765 =
                                  FStar_All.pipe_left
                                    (fun _0_17  ->
                                       FStar_Pervasives_Native.Some _0_17)
                                    (FStar_TypeChecker_Err.subtyping_failed
                                       env lc.FStar_Syntax_Syntax.res_typ t)
                                   in
                                let uu____7782 =
                                  FStar_TypeChecker_Env.set_range env
                                    e.FStar_Syntax_Syntax.pos
                                   in
                                let uu____7783 =
                                  FStar_Syntax_Util.lcomp_of_comp cret  in
                                let uu____7784 =
                                  FStar_All.pipe_left
                                    FStar_TypeChecker_Rel.guard_of_guard_formula
                                    (FStar_TypeChecker_Common.NonTrivial
                                       guard)
                                   in
                                strengthen_precondition uu____7765 uu____7782
                                  e uu____7783 uu____7784
                                 in
                              match uu____7760 with
                              | (eq_ret,_trivial_so_ok_to_discard) ->
                                  let x1 =
                                    let uu___117_7788 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___117_7788.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___117_7788.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort =
                                        (lc.FStar_Syntax_Syntax.res_typ)
                                    }  in
                                  let c1 =
                                    let uu____7790 =
                                      FStar_Syntax_Util.lcomp_of_comp c  in
                                    bind e.FStar_Syntax_Syntax.pos env
                                      (FStar_Pervasives_Native.Some e)
                                      uu____7790
                                      ((FStar_Pervasives_Native.Some x1),
                                        eq_ret)
                                     in
                                  let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                     in
                                  ((let uu____7795 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____7795
                                    then
                                      let uu____7796 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c2
                                         in
                                      FStar_Util.print1
                                        "Strengthened to %s\n" uu____7796
                                    else ());
                                   c2))))
                      in
                   let flags1 =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___86_7806  ->
                             match uu___86_7806 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____7809 -> []))
                      in
                   let lc1 =
                     let uu____7811 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name
                        in
                     FStar_Syntax_Syntax.mk_lcomp uu____7811 t flags1
                       strengthen
                      in
                   let g2 =
                     let uu___118_7813 = g1  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___118_7813.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___118_7813.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___118_7813.FStar_TypeChecker_Env.implicits)
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
        let uu____7848 =
          let uu____7851 =
            let uu____7856 =
              let uu____7857 =
                let uu____7864 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____7864  in
              [uu____7857]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____7856  in
          uu____7851 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____7848  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t
         in
      let uu____7885 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____7885
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____7901 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____7916 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____7932 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____7932
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____7946)::(ens,uu____7948)::uu____7949 ->
                    let uu____7978 =
                      let uu____7981 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____7981  in
                    let uu____7982 =
                      let uu____7983 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____7983  in
                    (uu____7978, uu____7982)
                | uu____7986 ->
                    let uu____7995 =
                      let uu____8000 =
                        let uu____8001 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____8001
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____8000)
                       in
                    FStar_Errors.raise_error uu____7995
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____8017)::uu____8018 ->
                    let uu____8037 =
                      let uu____8042 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____8042
                       in
                    (match uu____8037 with
                     | (us_r,uu____8074) ->
                         let uu____8075 =
                           let uu____8080 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____8080
                            in
                         (match uu____8075 with
                          | (us_e,uu____8112) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____8115 =
                                  let uu____8116 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8116
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8115
                                  us_r
                                 in
                              let as_ens =
                                let uu____8118 =
                                  let uu____8119 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8119
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8118
                                  us_e
                                 in
                              let req =
                                let uu____8123 =
                                  let uu____8128 =
                                    let uu____8129 =
                                      let uu____8138 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8138]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8129
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____8128
                                   in
                                uu____8123 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____8170 =
                                  let uu____8175 =
                                    let uu____8176 =
                                      let uu____8185 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8185]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8176
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____8175
                                   in
                                uu____8170 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____8214 =
                                let uu____8217 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____8217  in
                              let uu____8218 =
                                let uu____8219 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____8219  in
                              (uu____8214, uu____8218)))
                | uu____8222 -> failwith "Impossible"))
  
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
      (let uu____8252 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____8252
       then
         let uu____8253 = FStar_Syntax_Print.term_to_string tm  in
         let uu____8254 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____8253 uu____8254
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
        (let uu____8298 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____8298
         then
           let uu____8299 = FStar_Syntax_Print.term_to_string tm  in
           let uu____8300 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____8299
             uu____8300
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____8307 =
      let uu____8308 =
        let uu____8309 = FStar_Syntax_Subst.compress t  in
        uu____8309.FStar_Syntax_Syntax.n  in
      match uu____8308 with
      | FStar_Syntax_Syntax.Tm_app uu____8312 -> false
      | uu____8327 -> true  in
    if uu____8307
    then t
    else
      (let uu____8329 = FStar_Syntax_Util.head_and_args t  in
       match uu____8329 with
       | (head1,args) ->
           let uu____8360 =
             let uu____8361 =
               let uu____8362 = FStar_Syntax_Subst.compress head1  in
               uu____8362.FStar_Syntax_Syntax.n  in
             match uu____8361 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____8365 -> false  in
           if uu____8360
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____8387 ->
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
             let uu____8432 = FStar_Syntax_Util.arrow_formals t1  in
             match uu____8432 with
             | (formals,uu____8446) ->
                 let n_implicits =
                   let uu____8464 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____8542  ->
                             match uu____8542 with
                             | (uu____8549,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality))))
                      in
                   match uu____8464 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits
                    in
                 n_implicits
              in
           let inst_n_binders t1 =
             let uu____8682 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____8682 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t  in
                 let n_available = number_of_implicits t1  in
                 if n_available < n_expected
                 then
                   let uu____8706 =
                     let uu____8711 =
                       let uu____8712 = FStar_Util.string_of_int n_expected
                          in
                       let uu____8719 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____8720 = FStar_Util.string_of_int n_available
                          in
                       FStar_Util.format3
                         "Expected a term with %s implicit arguments, but %s has only %s"
                         uu____8712 uu____8719 uu____8720
                        in
                     (FStar_Errors.Fatal_MissingImplicitArguments,
                       uu____8711)
                      in
                   let uu____8727 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error uu____8706 uu____8727
                 else FStar_Pervasives_Native.Some (n_available - n_expected)
              in
           let decr_inst uu___87_8750 =
             match uu___87_8750 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
              in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____8780 = FStar_Syntax_Subst.open_comp bs c  in
               (match uu____8780 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_18,uu____8895) when
                          _0_18 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____8938,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____8971 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____8971 with
                           | (v1,uu____9011,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1  in
                               let uu____9030 =
                                 aux subst2 (decr_inst inst_n) rest  in
                               (match uu____9030 with
                                | (args,bs3,subst3,g') ->
                                    let uu____9123 =
                                      FStar_TypeChecker_Rel.conj_guard g g'
                                       in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____9123)))
                      | (uu____9150,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                       in
                    let uu____9196 =
                      let uu____9223 = inst_n_binders t  in
                      aux [] uu____9223 bs1  in
                    (match uu____9196 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____9294) -> (e, torig, guard)
                          | (uu____9325,[]) when
                              let uu____9356 =
                                FStar_Syntax_Util.is_total_comp c1  in
                              Prims.op_Negation uu____9356 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____9357 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____9385 ->
                                    FStar_Syntax_Util.arrow bs2 c1
                                 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1  in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              (e1, t2, guard))))
           | uu____9398 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____9408 =
      let uu____9411 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____9411
        (FStar_List.map
           (fun u  ->
              let uu____9421 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____9421 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____9408 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____9442 = FStar_Util.set_is_empty x  in
      if uu____9442
      then []
      else
        (let s =
           let uu____9457 =
             let uu____9468 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____9468  in
           FStar_All.pipe_right uu____9457 FStar_Util.set_elements  in
         (let uu____9500 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____9500
          then
            let uu____9501 =
              let uu____9502 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____9502  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____9501
          else ());
         (let r =
            let uu____9509 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____9509  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____9548 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____9548
                     then
                       let uu____9549 =
                         let uu____9550 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____9550
                          in
                       let uu____9551 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____9552 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____9549 uu____9551 uu____9552
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
        let uu____9578 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____9578 FStar_Util.set_elements  in
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
        | ([],uu____9616) -> generalized_univ_names
        | (uu____9623,[]) -> explicit_univ_names
        | uu____9630 ->
            let uu____9639 =
              let uu____9644 =
                let uu____9645 = FStar_Syntax_Print.term_to_string t  in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____9645
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____9644)
               in
            FStar_Errors.raise_error uu____9639 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____9663 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____9663
       then
         let uu____9664 = FStar_Syntax_Print.term_to_string t  in
         let uu____9665 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____9664 uu____9665
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____9671 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____9671
        then
          let uu____9672 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____9672
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____9678 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____9678
         then
           let uu____9679 = FStar_Syntax_Print.term_to_string t  in
           let uu____9680 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____9679 uu____9680
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
        let uu____9758 =
          let uu____9759 =
            FStar_Util.for_all
              (fun uu____9772  ->
                 match uu____9772 with
                 | (uu____9781,uu____9782,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____9759  in
        if uu____9758
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____9830 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____9830
              then
                let uu____9831 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____9831
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Exclude
                    FStar_TypeChecker_Normalize.Zeta;
                  FStar_TypeChecker_Normalize.NoFullNorm;
                  FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env c
                 in
              (let uu____9835 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____9835
               then
                 let uu____9836 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____9836
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____9851 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____9851 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____9887 =
             match uu____9887 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress
                    in
                 let c1 = norm1 c  in
                 let t1 = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t1  in
                 let uvt = FStar_Syntax_Free.uvars t1  in
                 ((let uu____9931 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____9931
                   then
                     let uu____9932 =
                       let uu____9933 =
                         let uu____9936 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____9936
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____9933
                         (FStar_String.concat ", ")
                        in
                     let uu____9979 =
                       let uu____9980 =
                         let uu____9983 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____9983
                           (FStar_List.map
                              (fun u  ->
                                 let uu____9994 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____9995 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____9994
                                   uu____9995))
                          in
                       FStar_All.pipe_right uu____9980
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____9932
                       uu____9979
                   else ());
                  (let univs2 =
                     let uu____10002 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____10014 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____10014) univs1
                       uu____10002
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____10021 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____10021
                    then
                      let uu____10022 =
                        let uu____10023 =
                          let uu____10026 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____10026
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____10023
                          (FStar_String.concat ", ")
                         in
                      let uu____10069 =
                        let uu____10070 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____10081 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____10082 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____10081
                                    uu____10082))
                           in
                        FStar_All.pipe_right uu____10070
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____10022 uu____10069
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____10096 =
             let uu____10113 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____10113  in
           match uu____10096 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____10205 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____10205
                 then ()
                 else
                   (let uu____10207 = lec_hd  in
                    match uu____10207 with
                    | (lb1,uu____10215,uu____10216) ->
                        let uu____10217 = lec2  in
                        (match uu____10217 with
                         | (lb2,uu____10225,uu____10226) ->
                             let msg =
                               let uu____10228 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10229 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____10228 uu____10229
                                in
                             let uu____10230 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____10230))
                  in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun u  ->
                           FStar_All.pipe_right u21
                             (FStar_Util.for_some
                                (fun u'  ->
                                   FStar_Syntax_Unionfind.equiv
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                     u'.FStar_Syntax_Syntax.ctx_uvar_head))))
                    in
                 let uu____10294 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____10294
                 then ()
                 else
                   (let uu____10296 = lec_hd  in
                    match uu____10296 with
                    | (lb1,uu____10304,uu____10305) ->
                        let uu____10306 = lec2  in
                        (match uu____10306 with
                         | (lb2,uu____10314,uu____10315) ->
                             let msg =
                               let uu____10317 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10318 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____10317 uu____10318
                                in
                             let uu____10319 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____10319))
                  in
               let lecs1 =
                 let uu____10329 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____10388 = univs_and_uvars_of_lec this_lec  in
                        match uu____10388 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____10329 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____10489 = lec_hd  in
                   match uu____10489 with
                   | (lbname,e,c) ->
                       let uu____10499 =
                         let uu____10504 =
                           let uu____10505 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____10506 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____10507 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____10505 uu____10506 uu____10507
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____10504)
                          in
                       let uu____10508 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____10499 uu____10508
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____10529 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____10529 with
                         | FStar_Pervasives_Native.Some uu____10538 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____10545 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.Exclude
                                   FStar_TypeChecker_Normalize.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____10549 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____10549 with
                              | (bs,kres) ->
                                  ((let uu____10587 =
                                      let uu____10588 =
                                        let uu____10591 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____10591
                                         in
                                      uu____10588.FStar_Syntax_Syntax.n  in
                                    match uu____10587 with
                                    | FStar_Syntax_Syntax.Tm_type uu____10592
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____10596 =
                                          let uu____10597 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____10597  in
                                        if uu____10596
                                        then fail1 kres
                                        else ()
                                    | uu____10599 -> fail1 kres);
                                   (let a =
                                      let uu____10601 =
                                        let uu____10604 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _0_19  ->
                                             FStar_Pervasives_Native.Some
                                               _0_19) uu____10604
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____10601
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____10612 ->
                                          let uu____10619 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____10619
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_tot
                                                  kres))
                                       in
                                    FStar_Syntax_Util.set_uvar
                                      u.FStar_Syntax_Syntax.ctx_uvar_head t;
                                    (a,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag)))))))
                  in
               let gen_univs1 = gen_univs env univs1  in
               let gen_tvars = gen_types uvs  in
               let ecs =
                 FStar_All.pipe_right lecs2
                   (FStar_List.map
                      (fun uu____10730  ->
                         match uu____10730 with
                         | (lbname,e,c) ->
                             let uu____10784 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____10859 ->
                                   let uu____10874 = (e, c)  in
                                   (match uu____10874 with
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
                                                (fun uu____10925  ->
                                                   match uu____10925 with
                                                   | (x,uu____10933) ->
                                                       let uu____10938 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____10938)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____10956 =
                                                let uu____10957 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____10957
                                                 in
                                              if uu____10956
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
                                          let uu____10963 =
                                            let uu____10964 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____10964.FStar_Syntax_Syntax.n
                                             in
                                          match uu____10963 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____10985 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____10985 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____10998 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____11002 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____11002, gen_tvars))
                                in
                             (match uu____10784 with
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
        (let uu____11156 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____11156
         then
           let uu____11157 =
             let uu____11158 =
               FStar_List.map
                 (fun uu____11171  ->
                    match uu____11171 with
                    | (lb,uu____11179,uu____11180) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____11158 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____11157
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____11201  ->
                match uu____11201 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____11230 = gen env is_rec lecs  in
           match uu____11230 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____11329  ->
                       match uu____11329 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____11391 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____11391
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____11437  ->
                           match uu____11437 with
                           | (l,us,e,c,gvs) ->
                               let uu____11471 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____11472 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____11473 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____11474 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____11475 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____11471 uu____11472 uu____11473
                                 uu____11474 uu____11475))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____11516  ->
                match uu____11516 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____11560 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____11560, t, c, gvs)) univnames_lecs
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
              (let uu____11617 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____11617 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____11623 = FStar_TypeChecker_Rel.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                     uu____11623)
             in
          let is_var e1 =
            let uu____11632 =
              let uu____11633 = FStar_Syntax_Subst.compress e1  in
              uu____11633.FStar_Syntax_Syntax.n  in
            match uu____11632 with
            | FStar_Syntax_Syntax.Tm_name uu____11636 -> true
            | uu____11637 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___119_11657 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___119_11657.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___119_11657.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____11658 -> e2  in
          let env2 =
            let uu___120_11660 = env1  in
            let uu____11661 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___120_11660.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___120_11660.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___120_11660.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___120_11660.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___120_11660.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___120_11660.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___120_11660.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___120_11660.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___120_11660.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___120_11660.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___120_11660.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___120_11660.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___120_11660.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___120_11660.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___120_11660.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___120_11660.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____11661;
              FStar_TypeChecker_Env.is_iface =
                (uu___120_11660.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___120_11660.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___120_11660.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___120_11660.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___120_11660.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___120_11660.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___120_11660.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___120_11660.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___120_11660.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___120_11660.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___120_11660.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___120_11660.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___120_11660.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___120_11660.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___120_11660.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___120_11660.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___120_11660.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___120_11660.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___120_11660.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___120_11660.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___120_11660.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____11662 = check1 env2 t1 t2  in
          match uu____11662 with
          | FStar_Pervasives_Native.None  ->
              let uu____11669 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____11674 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____11669 uu____11674
          | FStar_Pervasives_Native.Some g ->
              ((let uu____11681 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____11681
                then
                  let uu____11682 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____11682
                else ());
               (let uu____11684 = decorate e t2  in (uu____11684, g)))
  
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
        let uu____11716 = FStar_Syntax_Util.is_total_lcomp lc  in
        if uu____11716
        then
          let uu____11721 = discharge g1  in
          let uu____11722 = FStar_Syntax_Syntax.lcomp_comp lc  in
          (uu____11721, uu____11722)
        else
          (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
           let steps =
             [FStar_TypeChecker_Normalize.Beta;
             FStar_TypeChecker_Normalize.NoFullNorm;
             FStar_TypeChecker_Normalize.DoNotUnfoldPureLets]  in
           let c1 =
             let uu____11729 =
               let uu____11730 =
                 let uu____11731 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                 FStar_All.pipe_right uu____11731 FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____11730
                 (FStar_TypeChecker_Normalize.normalize_comp steps env)
                in
             FStar_All.pipe_right uu____11729
               (FStar_TypeChecker_Env.comp_to_comp_typ env)
              in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name
              in
           let uu____11733 = destruct_comp c1  in
           match uu____11733 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____11750 = FStar_TypeChecker_Env.get_range env  in
                 let uu____11751 =
                   let uu____11756 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial
                      in
                   let uu____11757 =
                     let uu____11758 = FStar_Syntax_Syntax.as_arg t  in
                     let uu____11765 =
                       let uu____11774 = FStar_Syntax_Syntax.as_arg wp  in
                       [uu____11774]  in
                     uu____11758 :: uu____11765  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____11756 uu____11757  in
                 uu____11751 FStar_Pervasives_Native.None uu____11750  in
               ((let uu____11802 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification")
                    in
                 if uu____11802
                 then
                   let uu____11803 = FStar_Syntax_Print.term_to_string vc  in
                   FStar_Util.print1 "top-level VC: %s\n" uu____11803
                 else ());
                (let g2 =
                   let uu____11806 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc)
                      in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____11806  in
                 let uu____11807 = discharge g2  in
                 let uu____11808 = FStar_Syntax_Syntax.mk_Comp c1  in
                 (uu____11807, uu____11808))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___88_11840 =
        match uu___88_11840 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____11848)::[] -> f fst1
        | uu____11865 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____11876 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____11876
          (fun _0_21  -> FStar_TypeChecker_Common.NonTrivial _0_21)
         in
      let op_or_e e =
        let uu____11887 =
          let uu____11888 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____11888  in
        FStar_All.pipe_right uu____11887
          (fun _0_22  -> FStar_TypeChecker_Common.NonTrivial _0_22)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_23  -> FStar_TypeChecker_Common.NonTrivial _0_23)
         in
      let op_or_t t =
        let uu____11907 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____11907
          (fun _0_24  -> FStar_TypeChecker_Common.NonTrivial _0_24)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_25  -> FStar_TypeChecker_Common.NonTrivial _0_25)
         in
      let short_op_ite uu___89_11921 =
        match uu___89_11921 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____11929)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____11948)::[] ->
            let uu____11977 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____11977
              (fun _0_26  -> FStar_TypeChecker_Common.NonTrivial _0_26)
        | uu____11978 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____11989 =
          let uu____11997 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____11997)  in
        let uu____12005 =
          let uu____12015 =
            let uu____12023 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____12023)  in
          let uu____12031 =
            let uu____12041 =
              let uu____12049 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____12049)  in
            let uu____12057 =
              let uu____12067 =
                let uu____12075 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____12075)  in
              let uu____12083 =
                let uu____12093 =
                  let uu____12101 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____12101)  in
                [uu____12093; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____12067 :: uu____12083  in
            uu____12041 :: uu____12057  in
          uu____12015 :: uu____12031  in
        uu____11989 :: uu____12005  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____12163 =
            FStar_Util.find_map table
              (fun uu____12178  ->
                 match uu____12178 with
                 | (x,mk1) ->
                     let uu____12195 = FStar_Ident.lid_equals x lid  in
                     if uu____12195
                     then
                       let uu____12198 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____12198
                     else FStar_Pervasives_Native.None)
             in
          (match uu____12163 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____12201 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____12207 =
      let uu____12208 = FStar_Syntax_Util.un_uinst l  in
      uu____12208.FStar_Syntax_Syntax.n  in
    match uu____12207 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____12212 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____12242)::uu____12243 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____12254 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____12261,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____12262))::uu____12263 -> bs
      | uu____12274 ->
          let uu____12275 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____12275 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____12279 =
                 let uu____12280 = FStar_Syntax_Subst.compress t  in
                 uu____12280.FStar_Syntax_Syntax.n  in
               (match uu____12279 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____12284) ->
                    let uu____12301 =
                      FStar_Util.prefix_until
                        (fun uu___90_12341  ->
                           match uu___90_12341 with
                           | (uu____12348,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____12349)) ->
                               false
                           | uu____12352 -> true) bs'
                       in
                    (match uu____12301 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____12387,uu____12388) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____12460,uu____12461) ->
                         let uu____12534 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____12552  ->
                                   match uu____12552 with
                                   | (x,uu____12560) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____12534
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____12597  ->
                                     match uu____12597 with
                                     | (x,i) ->
                                         let uu____12608 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____12608, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____12614 -> bs))
  
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
            let uu____12642 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____12642
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
          let uu____12669 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____12669
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
        (let uu____12704 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____12704
         then
           ((let uu____12706 = FStar_Ident.text_of_lid lident  in
             d uu____12706);
            (let uu____12707 = FStar_Ident.text_of_lid lident  in
             let uu____12708 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____12707 uu____12708))
         else ());
        (let fv =
           let uu____12711 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____12711
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
         let uu____12721 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___121_12723 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___121_12723.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___121_12723.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___121_12723.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___121_12723.FStar_Syntax_Syntax.sigattrs)
           }), uu____12721))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___91_12739 =
        match uu___91_12739 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____12740 -> false  in
      let reducibility uu___92_12746 =
        match uu___92_12746 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____12747 -> false  in
      let assumption uu___93_12753 =
        match uu___93_12753 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____12754 -> false  in
      let reification uu___94_12760 =
        match uu___94_12760 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____12761 -> true
        | uu____12762 -> false  in
      let inferred uu___95_12768 =
        match uu___95_12768 with
        | FStar_Syntax_Syntax.Discriminator uu____12769 -> true
        | FStar_Syntax_Syntax.Projector uu____12770 -> true
        | FStar_Syntax_Syntax.RecordType uu____12775 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____12784 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____12793 -> false  in
      let has_eq uu___96_12799 =
        match uu___96_12799 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____12800 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____12864 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____12869 -> true  in
      let quals = FStar_Syntax_Util.quals_of_sigelt se  in
      let uu____12873 =
        let uu____12874 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___97_12878  ->
                  match uu___97_12878 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____12879 -> false))
           in
        FStar_All.pipe_right uu____12874 Prims.op_Negation  in
      if uu____12873
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____12894 =
            let uu____12899 =
              let uu____12900 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____12900 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____12899)  in
          FStar_Errors.raise_error uu____12894 r  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____12912 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____12916 =
            let uu____12917 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____12917  in
          if uu____12916 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____12922),uu____12923) ->
              ((let uu____12933 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____12933
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____12937 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____12937
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____12943 ->
              let uu____12952 =
                let uu____12953 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x)))
                   in
                Prims.op_Negation uu____12953  in
              if uu____12952 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____12959 ->
              let uu____12966 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____12966 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____12970 ->
              let uu____12977 =
                let uu____12978 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____12978  in
              if uu____12977 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____12984 ->
              let uu____12985 =
                let uu____12986 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____12986  in
              if uu____12985 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12992 ->
              let uu____12993 =
                let uu____12994 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____12994  in
              if uu____12993 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13000 ->
              let uu____13013 =
                let uu____13014 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____13014  in
              if uu____13013 then err'1 () else ()
          | uu____13020 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec aux_whnf env t1 =
        let uu____13054 =
          let uu____13055 = FStar_Syntax_Subst.compress t1  in
          uu____13055.FStar_Syntax_Syntax.n  in
        match uu____13054 with
        | FStar_Syntax_Syntax.Tm_type uu____13058 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (let uu____13061 =
                 let uu____13066 =
                   FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
                 FStar_All.pipe_right uu____13066
                   (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
                  in
               FStar_All.pipe_right uu____13061
                 (fun l_opt  ->
                    (FStar_Util.is_some l_opt) &&
                      (let uu____13084 =
                         FStar_All.pipe_right l_opt FStar_Util.must  in
                       FStar_All.pipe_right uu____13084
                         (FStar_List.existsb
                            (fun t2  ->
                               let uu____13101 =
                                 let uu____13102 =
                                   FStar_Syntax_Subst.compress t2  in
                                 uu____13102.FStar_Syntax_Syntax.n  in
                               match uu____13101 with
                               | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                   FStar_Ident.lid_equals
                                     (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     FStar_Parser_Const.must_erase_for_extraction_attr
                                   -> true
                               | uu____13106 -> false)))))
        | FStar_Syntax_Syntax.Tm_arrow uu____13107 ->
            let uu____13120 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____13120 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____13146 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____13146
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____13148;
               FStar_Syntax_Syntax.index = uu____13149;
               FStar_Syntax_Syntax.sort = t2;_},uu____13151)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____13159,uu____13160) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____13202::[]) ->
            let uu____13233 =
              let uu____13234 = FStar_Syntax_Util.un_uinst head1  in
              uu____13234.FStar_Syntax_Syntax.n  in
            (match uu____13233 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.erased_lid
             | uu____13238 -> false)
        | uu____13239 -> false
      
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
        (let uu____13247 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____13247
         then
           let uu____13248 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____13248
         else ());
        res
       in aux g t
  