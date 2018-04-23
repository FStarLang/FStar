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
        FStar_Syntax_Syntax.binders ->
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
              let uu____67 = FStar_Syntax_Unionfind.fresh ()  in
              {
                FStar_Syntax_Syntax.ctx_uvar_head = uu____67;
                FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                FStar_Syntax_Syntax.ctx_uvar_typ = k;
                FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                FStar_Syntax_Syntax.ctx_uvar_should_check = true;
                FStar_Syntax_Syntax.ctx_uvar_range = r
              }  in
            FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r true
              gamma binders;
            (let uu____79 =
               FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_uvar)
                 FStar_Pervasives_Native.None r
                in
             (ctx_uvar, uu____79))
  
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
          let uu____116 =
            FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid  in
          match uu____116 with
          | FStar_Pervasives_Native.Some (uu____139::(tm,uu____141)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                 in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____191 ->
              let binders = FStar_TypeChecker_Env.all_binders env  in
              let uu____203 =
                new_implicit_var_aux reason r env.FStar_TypeChecker_Env.gamma
                  binders k
                 in
              (match uu____203 with
               | (ctx_uvar,t) ->
                   let g =
                     let uu___98_229 = FStar_TypeChecker_Rel.trivial_guard
                        in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___98_229.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___98_229.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___98_229.FStar_TypeChecker_Env.univ_ineqs);
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
          let uu____328 = i  in
          match uu____328 with
          | (reason,term,ctx_u,range,should_check) ->
              if Prims.op_Negation should_check
              then i
              else
                (let uu____375 =
                   FStar_Syntax_Unionfind.find
                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 match uu____375 with
                 | FStar_Pervasives_Native.Some uu____390 -> i
                 | FStar_Pervasives_Native.None  ->
                     let uu____391 =
                       FStar_Util.prefix_until
                         (fun uu___79_406  ->
                            match uu___79_406 with
                            | FStar_Syntax_Syntax.Binding_var uu____407 ->
                                true
                            | uu____408 -> false)
                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma
                        in
                     (match uu____391 with
                      | FStar_Pervasives_Native.None  -> i
                      | FStar_Pervasives_Native.Some
                          (uu____431,hd1,gamma_tail) ->
                          (FStar_TypeChecker_Common.check_uvar_ctx_invariant
                             reason range should_check
                             ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma
                             ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders;
                           (match hd1 with
                            | FStar_Syntax_Syntax.Binding_var x' when
                                FStar_Syntax_Syntax.bv_eq x x' ->
                                let uu____466 =
                                  FStar_Util.prefix
                                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                   in
                                (match uu____466 with
                                 | (binders_pfx,uu____498) ->
                                     let typ =
                                       let uu____522 =
                                         let uu____529 =
                                           FStar_Syntax_Syntax.mk_binder x
                                            in
                                         [uu____529]  in
                                       let uu____542 =
                                         FStar_Syntax_Syntax.mk_Total
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                          in
                                       FStar_Syntax_Util.arrow uu____522
                                         uu____542
                                        in
                                     let uu____543 =
                                       new_implicit_var_aux reason range
                                         gamma_tail binders_pfx typ
                                        in
                                     (match uu____543 with
                                      | (ctx_v,t_v) ->
                                          let sol =
                                            let uu____571 =
                                              let uu____576 =
                                                let uu____577 =
                                                  let uu____584 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      x
                                                     in
                                                  FStar_Syntax_Syntax.as_arg
                                                    uu____584
                                                   in
                                                [uu____577]  in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                t_v uu____576
                                               in
                                            uu____571
                                              FStar_Pervasives_Native.None
                                              range
                                             in
                                          ((let uu____600 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env)
                                                (FStar_Options.Other "Rel")
                                               in
                                            if uu____600
                                            then
                                              let uu____601 =
                                                FStar_Syntax_Print.ctx_uvar_to_string
                                                  ctx_u
                                                 in
                                              let uu____602 =
                                                FStar_Syntax_Print.term_to_string
                                                  sol
                                                 in
                                              FStar_Util.print2
                                                "Closing implicits %s to %s"
                                                uu____601 uu____602
                                            else ());
                                           FStar_Syntax_Unionfind.change
                                             ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                             sol;
                                           (reason, t_v, ctx_v, range,
                                             should_check))))
                            | uu____607 -> i))))
           in
        let uu____608 =
          FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred
            (FStar_List.partition
               (fun uu____630  ->
                  match uu____630 with
                  | (uu____635,p) ->
                      FStar_TypeChecker_Rel.flex_prob_closing env xs p))
           in
        match uu____608 with
        | (solve_now,defer) ->
            let g1 =
              FStar_TypeChecker_Rel.solve_deferred_constraints env
                (let uu___99_641 = g  in
                 {
                   FStar_TypeChecker_Env.guard_f =
                     (uu___99_641.FStar_TypeChecker_Env.guard_f);
                   FStar_TypeChecker_Env.deferred = solve_now;
                   FStar_TypeChecker_Env.univ_ineqs =
                     (uu___99_641.FStar_TypeChecker_Env.univ_ineqs);
                   FStar_TypeChecker_Env.implicits =
                     (uu___99_641.FStar_TypeChecker_Env.implicits)
                 })
               in
            let g2 =
              let uu___100_643 = g1  in
              {
                FStar_TypeChecker_Env.guard_f =
                  (uu___100_643.FStar_TypeChecker_Env.guard_f);
                FStar_TypeChecker_Env.deferred = defer;
                FStar_TypeChecker_Env.univ_ineqs =
                  (uu___100_643.FStar_TypeChecker_Env.univ_ineqs);
                FStar_TypeChecker_Env.implicits =
                  (uu___100_643.FStar_TypeChecker_Env.implicits)
              }  in
            let is =
              FStar_List.fold_left
                (fun is  ->
                   fun uu____682  ->
                     match uu____682 with
                     | (x,uu____716) -> FStar_List.map (aux x) is)
                g2.FStar_TypeChecker_Env.implicits xs
               in
            let g3 =
              let uu___101_742 = g2  in
              {
                FStar_TypeChecker_Env.guard_f =
                  (uu___101_742.FStar_TypeChecker_Env.guard_f);
                FStar_TypeChecker_Env.deferred =
                  (uu___101_742.FStar_TypeChecker_Env.deferred);
                FStar_TypeChecker_Env.univ_ineqs =
                  (uu___101_742.FStar_TypeChecker_Env.univ_ineqs);
                FStar_TypeChecker_Env.implicits = is
              }  in
            ((let uu____744 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____744
              then
                let uu____745 = FStar_TypeChecker_Rel.guard_to_string env g3
                   in
                FStar_Util.print1 "Closed implicits, guard is\n\t%s\n"
                  uu____745
              else ());
             g3)
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____760 =
        let uu____761 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____761  in
      if uu____760
      then
        let us =
          let uu____763 =
            let uu____766 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____766
             in
          FStar_All.pipe_right uu____763 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____777 =
            let uu____782 =
              let uu____783 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____783
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____782)  in
          FStar_Errors.log_issue r uu____777);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.typ,Prims.bool,
        FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple4)
  =
  fun env  ->
    fun uu____802  ->
      match uu____802 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____814;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____816;
          FStar_Syntax_Syntax.lbpos = uu____817;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____854 = FStar_Syntax_Subst.open_univ_vars univ_vars1 e
                  in
               (match uu____854 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let mk_binder1 env2 a =
                      let uu____890 =
                        let uu____891 =
                          FStar_Syntax_Subst.compress
                            a.FStar_Syntax_Syntax.sort
                           in
                        uu____891.FStar_Syntax_Syntax.n  in
                      match uu____890 with
                      | FStar_Syntax_Syntax.Tm_unknown  ->
                          let uu____900 = FStar_Syntax_Util.type_u ()  in
                          (match uu____900 with
                           | (k,uu____912) ->
                               let uu____913 =
                                 new_implicit_var ""
                                   e1.FStar_Syntax_Syntax.pos env2 k
                                  in
                               (match uu____913 with
                                | (t2,uu____933,guard) ->
                                    ((let uu___102_948 = a  in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___102_948.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___102_948.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t2
                                      }), false, guard)))
                      | uu____949 ->
                          (a, true, FStar_TypeChecker_Rel.trivial_guard)
                       in
                    let rec aux must_check_ty env2 e2 g =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____1003) ->
                          aux must_check_ty env2 e4 g
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____1010) ->
                          ((FStar_Pervasives_Native.fst t2), true, g)
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1069) ->
                          let uu____1090 =
                            FStar_All.pipe_right bs
                              (FStar_List.fold_left
                                 (fun uu____1159  ->
                                    fun uu____1160  ->
                                      match (uu____1159, uu____1160) with
                                      | ((env3,bs1,must_check_ty1,g1),
                                         (a,imp)) ->
                                          let uu____1247 =
                                            if must_check_ty1
                                            then
                                              (a, true,
                                                FStar_TypeChecker_Rel.trivial_guard)
                                            else mk_binder1 env3 a  in
                                          (match uu____1247 with
                                           | (tb,must_check_ty2,g_a) ->
                                               let b = (tb, imp)  in
                                               let bs2 =
                                                 FStar_List.append bs1 [b]
                                                  in
                                               let env4 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env3 [b]
                                                  in
                                               let uu____1311 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   g_a g1
                                                  in
                                               (env4, bs2, must_check_ty2,
                                                 uu____1311)))
                                 (env2, [], must_check_ty, g))
                             in
                          (match uu____1090 with
                           | (env3,bs1,must_check_ty1,g1) ->
                               let uu____1354 =
                                 aux must_check_ty1 env3 body g1  in
                               (match uu____1354 with
                                | (res,must_check_ty2,g2) ->
                                    let c =
                                      match res with
                                      | FStar_Util.Inl t2 ->
                                          let uu____1388 =
                                            FStar_Options.ml_ish ()  in
                                          if uu____1388
                                          then FStar_Syntax_Util.ml_comp t2 r
                                          else
                                            FStar_Syntax_Syntax.mk_Total t2
                                      | FStar_Util.Inr c -> c  in
                                    let t2 = FStar_Syntax_Util.arrow bs1 c
                                       in
                                    ((let uu____1395 =
                                        FStar_TypeChecker_Env.debug env3
                                          FStar_Options.High
                                         in
                                      if uu____1395
                                      then
                                        let uu____1396 =
                                          FStar_Range.string_of_range r  in
                                        let uu____1397 =
                                          FStar_Syntax_Print.term_to_string
                                            t2
                                           in
                                        let uu____1398 =
                                          FStar_Util.string_of_bool
                                            must_check_ty2
                                           in
                                        FStar_Util.print3
                                          "(%s) Using type %s .... must check = %s\n"
                                          uu____1396 uu____1397 uu____1398
                                      else ());
                                     ((FStar_Util.Inl t2), must_check_ty2,
                                       g2))))
                      | uu____1406 ->
                          if must_check_ty
                          then
                            ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true,
                              g)
                          else
                            (let uu____1422 =
                               new_implicit_var "" r env2
                                 FStar_Syntax_Util.ktype0
                                in
                             match uu____1422 with
                             | (t2,uu____1446,g') ->
                                 let uu____1460 =
                                   FStar_TypeChecker_Rel.conj_guard g g'  in
                                 ((FStar_Util.Inl t2), false, uu____1460))
                       in
                    let uu____1465 =
                      aux false env1 e1 FStar_TypeChecker_Rel.trivial_guard
                       in
                    (match uu____1465 with
                     | (t2,b,g) ->
                         let t3 =
                           match t2 with
                           | FStar_Util.Inr c ->
                               let uu____1499 =
                                 FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                               if uu____1499
                               then FStar_Syntax_Util.comp_result c
                               else
                                 (let uu____1501 =
                                    let uu____1506 =
                                      let uu____1507 =
                                        FStar_Syntax_Print.comp_to_string c
                                         in
                                      FStar_Util.format1
                                        "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                        uu____1507
                                       in
                                    (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                      uu____1506)
                                     in
                                  FStar_Errors.raise_error uu____1501 rng)
                           | FStar_Util.Inl t3 -> t3  in
                         (univ_vars2, t3, b, g)))
           | uu____1511 ->
               let uu____1512 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____1512 with
                | (univ_vars2,t2) ->
                    (univ_vars2, t2, false,
                      FStar_TypeChecker_Rel.trivial_guard)))
  
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
            let uu____1608 =
              let uu____1613 =
                FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
              match uu____1613 with
              | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____1618;
                  FStar_Syntax_Syntax.vars = uu____1619;_} ->
                  let uu____1622 = FStar_Syntax_Util.type_u ()  in
                  (match uu____1622 with
                   | (t,uu____1632) ->
                       let uu____1633 =
                         let uu____1646 = FStar_Syntax_Syntax.range_of_bv x
                            in
                         new_implicit_var "" uu____1646 env1 t  in
                       (match uu____1633 with | (t1,uu____1652,g) -> (t1, g)))
              | t -> tc_annot env1 t  in
            match uu____1608 with
            | (t_x,guard) ->
                ((let uu___103_1674 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___103_1674.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___103_1674.FStar_Syntax_Syntax.index);
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
                  | uu____1749 ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant c)
                        FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                   in
                ([], [], [], env1, e, FStar_TypeChecker_Rel.trivial_guard,
                  p1)
            | FStar_Syntax_Syntax.Pat_dot_term (x,uu____1757) ->
                let uu____1762 = FStar_Syntax_Util.type_u ()  in
                (match uu____1762 with
                 | (k,uu____1788) ->
                     let uu____1789 =
                       let uu____1802 = FStar_Syntax_Syntax.range_of_bv x  in
                       new_implicit_var "" uu____1802 env1 k  in
                     (match uu____1789 with
                      | (t,uu____1824,g) ->
                          let x1 =
                            let uu___104_1839 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___104_1839.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___104_1839.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t
                            }  in
                          let uu____1840 =
                            let uu____1853 =
                              FStar_Syntax_Syntax.range_of_bv x1  in
                            new_implicit_var "" uu____1853 env1 t  in
                          (match uu____1840 with
                           | (e,uu____1875,g') ->
                               let p2 =
                                 let uu___105_1892 = p1  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_dot_term
                                        (x1, e));
                                   FStar_Syntax_Syntax.p =
                                     (uu___105_1892.FStar_Syntax_Syntax.p)
                                 }  in
                               let uu____1895 =
                                 FStar_TypeChecker_Rel.conj_guard g g'  in
                               ([], [], [], env1, e, uu____1895, p2))))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let uu____1903 = check_bv env1 x  in
                (match uu____1903 with
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
                let uu____1942 = check_bv env1 x  in
                (match uu____1942 with
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
                let uu____1997 =
                  FStar_All.pipe_right pats
                    (FStar_List.fold_left
                       (fun uu____2143  ->
                          fun uu____2144  ->
                            match (uu____2143, uu____2144) with
                            | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                                let uu____2342 =
                                  pat_as_arg_with_env allow_wc_dependence
                                    env2 p2
                                   in
                                (match uu____2342 with
                                 | (b',a',w',env3,te,guard',pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te  in
                                     let uu____2418 =
                                       FStar_TypeChecker_Rel.conj_guard guard
                                         guard'
                                        in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), uu____2418, ((pat, imp)
                                       :: pats1))))
                       ([], [], [], env1, [],
                         FStar_TypeChecker_Rel.trivial_guard, []))
                   in
                (match uu____1997 with
                 | (b,a,w,env2,args,guard,pats1) ->
                     let e =
                       let uu____2561 =
                         let uu____2566 = FStar_Syntax_Syntax.fv_to_tm fv  in
                         let uu____2567 =
                           FStar_All.pipe_right args FStar_List.rev  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2566 uu____2567
                          in
                       uu____2561 FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     let uu____2584 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten
                        in
                     let uu____2595 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten
                        in
                     let uu____2606 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten
                        in
                     (uu____2584, uu____2595, uu____2606, env2, e, guard,
                       (let uu___106_2624 = p1  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___106_2624.FStar_Syntax_Syntax.p)
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
                    (fun uu____2722  ->
                       match uu____2722 with
                       | (p2,imp) ->
                           let uu____2741 = elaborate_pat env1 p2  in
                           (uu____2741, imp)) pats
                   in
                let uu____2746 =
                  FStar_TypeChecker_Env.lookup_datacon env1
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____2746 with
                 | (uu____2753,t) ->
                     let uu____2755 = FStar_Syntax_Util.arrow_formals t  in
                     (match uu____2755 with
                      | (f,uu____2771) ->
                          let rec aux formals pats2 =
                            match (formals, pats2) with
                            | ([],[]) -> []
                            | ([],uu____2897::uu____2898) ->
                                let uu____2941 =
                                  FStar_Ident.range_of_lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_TooManyPatternArguments,
                                    "Too many pattern arguments") uu____2941
                            | (uu____2950::uu____2951,[]) ->
                                FStar_All.pipe_right formals
                                  (FStar_List.map
                                     (fun uu____3029  ->
                                        match uu____3029 with
                                        | (t1,imp) ->
                                            (match imp with
                                             | FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Syntax.Implicit
                                                 inaccessible) ->
                                                 let a =
                                                   let uu____3056 =
                                                     let uu____3059 =
                                                       FStar_Syntax_Syntax.range_of_bv
                                                         t1
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____3059
                                                      in
                                                   FStar_Syntax_Syntax.new_bv
                                                     uu____3056
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let r =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 let uu____3061 =
                                                   maybe_dot inaccessible a r
                                                    in
                                                 (uu____3061, true)
                                             | uu____3066 ->
                                                 let uu____3069 =
                                                   let uu____3074 =
                                                     let uu____3075 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1
                                                        in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____3075
                                                      in
                                                   (FStar_Errors.Fatal_InsufficientPatternArguments,
                                                     uu____3074)
                                                    in
                                                 let uu____3076 =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____3069 uu____3076)))
                            | (f1::formals',(p2,p_imp)::pats') ->
                                (match f1 with
                                 | (uu____3150,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    uu____3151)) when p_imp ->
                                     let uu____3154 = aux formals' pats'  in
                                     (p2, true) :: uu____3154
                                 | (uu____3171,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    inaccessible)) ->
                                     let a =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p2.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     let p3 =
                                       let uu____3179 =
                                         FStar_Ident.range_of_lid
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          in
                                       maybe_dot inaccessible a uu____3179
                                        in
                                     let uu____3180 = aux formals' pats2  in
                                     (p3, true) :: uu____3180
                                 | (uu____3197,imp) ->
                                     let uu____3203 =
                                       let uu____3210 =
                                         FStar_Syntax_Syntax.is_implicit imp
                                          in
                                       (p2, uu____3210)  in
                                     let uu____3213 = aux formals' pats'  in
                                     uu____3203 :: uu____3213)
                             in
                          let uu___107_3228 = p1  in
                          let uu____3231 =
                            let uu____3232 =
                              let uu____3245 = aux f pats1  in
                              (fv, uu____3245)  in
                            FStar_Syntax_Syntax.Pat_cons uu____3232  in
                          {
                            FStar_Syntax_Syntax.v = uu____3231;
                            FStar_Syntax_Syntax.p =
                              (uu___107_3228.FStar_Syntax_Syntax.p)
                          }))
            | uu____3262 -> p1  in
          let one_pat allow_wc_dependence env1 p1 =
            let p2 = elaborate_pat env1 p1  in
            let uu____3304 = pat_as_arg_with_env allow_wc_dependence env1 p2
               in
            match uu____3304 with
            | (b,a,w,env2,arg,guard,p3) ->
                let uu____3362 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                   in
                (match uu____3362 with
                 | FStar_Pervasives_Native.Some x ->
                     let uu____3388 =
                       FStar_TypeChecker_Err.nonlinear_pattern_variable x  in
                     FStar_Errors.raise_error uu____3388
                       p3.FStar_Syntax_Syntax.p
                 | uu____3411 -> (b, a, w, arg, guard, p3))
             in
          let uu____3420 = one_pat true env p  in
          match uu____3420 with
          | (b,uu____3450,uu____3451,tm,guard,p1) -> (b, tm, guard, p1)
  
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
          | (uu____3513,FStar_Syntax_Syntax.Tm_uinst (e2,uu____3515)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____3520,uu____3521) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____3525 =
                    let uu____3526 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____3527 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____3526 uu____3527
                     in
                  failwith uu____3525)
               else ();
               (let uu____3530 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat")
                   in
                if uu____3530
                then
                  let uu____3531 = FStar_Syntax_Print.bv_to_string x  in
                  let uu____3532 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____3531
                    uu____3532
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___108_3536 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___108_3536.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___108_3536.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____3540 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation
                   in
                if uu____3540
                then
                  let uu____3541 =
                    let uu____3542 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____3543 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____3542 uu____3543
                     in
                  failwith uu____3541
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___109_3547 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___109_3547.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___109_3547.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____3549),uu____3550) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____3574 =
                  let uu____3575 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  Prims.op_Negation uu____3575  in
                if uu____3574
                then
                  let uu____3576 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3576
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____3595;
                FStar_Syntax_Syntax.vars = uu____3596;_},args))
              ->
              ((let uu____3635 =
                  let uu____3636 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____3636 Prims.op_Negation  in
                if uu____3635
                then
                  let uu____3637 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3637
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3779)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3854) ->
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
                       | ((e2,imp),uu____3891) ->
                           let pat =
                             let uu____3913 = aux argpat e2  in
                             let uu____3914 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3913, uu____3914)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3919 ->
                      let uu____3942 =
                        let uu____3943 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3944 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3943 uu____3944
                         in
                      failwith uu____3942
                   in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____3956;
                     FStar_Syntax_Syntax.vars = uu____3957;_},uu____3958);
                FStar_Syntax_Syntax.pos = uu____3959;
                FStar_Syntax_Syntax.vars = uu____3960;_},args))
              ->
              ((let uu____4003 =
                  let uu____4004 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____4004 Prims.op_Negation  in
                if uu____4003
                then
                  let uu____4005 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____4005
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____4147)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____4222) ->
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
                       | ((e2,imp),uu____4259) ->
                           let pat =
                             let uu____4281 = aux argpat e2  in
                             let uu____4282 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____4281, uu____4282)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____4287 ->
                      let uu____4310 =
                        let uu____4311 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____4312 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____4311 uu____4312
                         in
                      failwith uu____4310
                   in
                match_args [] args argpats))
          | uu____4321 ->
              let uu____4326 =
                let uu____4327 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p  in
                let uu____4328 = FStar_Syntax_Print.pat_to_string qq  in
                let uu____4329 = FStar_Syntax_Print.term_to_string exp  in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____4327 uu____4328 uu____4329
                 in
              failwith uu____4326
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
    let pat_as_arg uu____4372 =
      match uu____4372 with
      | (p,i) ->
          let uu____4389 = decorated_pattern_as_term p  in
          (match uu____4389 with
           | (vars,te) ->
               let uu____4412 =
                 let uu____4417 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____4417)  in
               (vars, uu____4412))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____4431 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____4431)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____4435 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____4435)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____4439 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____4439)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____4460 =
          let uu____4477 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____4477 FStar_List.unzip  in
        (match uu____4460 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____4591 =
               let uu____4592 =
                 let uu____4593 =
                   let uu____4608 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____4608, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____4593  in
               mk1 uu____4592  in
             (vars1, uu____4591))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____4644,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____4654,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____4668 -> FStar_Pervasives_Native.Some hd1)
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____4690)::[] -> wp
      | uu____4707 ->
          let uu____4716 =
            let uu____4717 =
              let uu____4718 =
                FStar_List.map
                  (fun uu____4728  ->
                     match uu____4728 with
                     | (x,uu____4734) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____4718 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____4717
             in
          failwith uu____4716
       in
    let uu____4737 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____4737, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____4753 = destruct_comp c  in
        match uu____4753 with
        | (u,uu____4761,wp) ->
            let uu____4763 =
              let uu____4772 =
                let uu____4779 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____4779  in
              [uu____4772]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____4763;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____4807 =
          let uu____4814 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____4815 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____4814 uu____4815  in
        match uu____4807 with | (m,uu____4817,uu____4818) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____4834 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____4834
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
        let uu____4877 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____4877 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____4914 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____4914 with
             | (a,kwp) ->
                 let uu____4945 = destruct_comp m1  in
                 let uu____4952 = destruct_comp m2  in
                 ((md, a, kwp), uu____4945, uu____4952))
  
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
            let uu____5032 =
              let uu____5033 =
                let uu____5042 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____5042]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____5033;
                FStar_Syntax_Syntax.flags = flags1
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____5032
  
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
          let uu____5114 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____5114
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
      let uu____5126 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____5126
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____5129  ->
           let uu____5130 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____5130)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5136 =
      let uu____5137 = FStar_Syntax_Subst.compress t  in
      uu____5137.FStar_Syntax_Syntax.n  in
    match uu____5136 with
    | FStar_Syntax_Syntax.Tm_arrow uu____5140 -> true
    | uu____5153 -> false
  
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
              let uu____5210 =
                let uu____5211 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____5211  in
              if uu____5210
              then f
              else (let uu____5213 = reason1 ()  in label uu____5213 r f)
  
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
            let uu___110_5230 = g  in
            let uu____5231 =
              let uu____5232 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____5232  in
            {
              FStar_TypeChecker_Env.guard_f = uu____5231;
              FStar_TypeChecker_Env.deferred =
                (uu___110_5230.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___110_5230.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___110_5230.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____5252 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5252
        then c
        else
          (let uu____5254 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____5254
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____5313 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____5313]  in
                       let us =
                         let uu____5329 =
                           let uu____5332 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____5332]  in
                         u_res :: uu____5329  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____5338 =
                         let uu____5343 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____5344 =
                           let uu____5345 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____5352 =
                             let uu____5361 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____5368 =
                               let uu____5377 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____5377]  in
                             uu____5361 :: uu____5368  in
                           uu____5345 :: uu____5352  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____5343 uu____5344
                          in
                       uu____5338 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____5411 = destruct_comp c1  in
              match uu____5411 with
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
          (fun uu____5446  ->
             let uu____5447 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____5447)
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___80_5456  ->
            match uu___80_5456 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____5457 -> false))
  
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
                (let uu____5479 =
                   FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ
                    in
                 Prims.op_Negation uu____5479))
               &&
               (let uu____5486 = FStar_Syntax_Util.head_and_args' e  in
                match uu____5486 with
                | (head1,uu____5500) ->
                    let uu____5517 =
                      let uu____5518 = FStar_Syntax_Util.un_uinst head1  in
                      uu____5518.FStar_Syntax_Syntax.n  in
                    (match uu____5517 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____5522 =
                           let uu____5523 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____5523
                            in
                         Prims.op_Negation uu____5522
                     | uu____5524 -> true)))
              &&
              (let uu____5526 = should_not_inline_lc lc  in
               Prims.op_Negation uu____5526)
  
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
            let uu____5560 =
              let uu____5561 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____5561  in
            if uu____5560
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____5563 = FStar_Syntax_Util.is_unit t  in
               if uu____5563
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
                    let uu____5569 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____5569
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____5571 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____5571 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____5581 =
                             let uu____5582 =
                               let uu____5587 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____5588 =
                                 let uu____5589 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____5596 =
                                   let uu____5605 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____5605]  in
                                 uu____5589 :: uu____5596  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____5587
                                 uu____5588
                                in
                             uu____5582 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.NoFullNorm] env
                             uu____5581)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____5633 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____5633
           then
             let uu____5634 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____5635 = FStar_Syntax_Print.term_to_string v1  in
             let uu____5636 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____5634 uu____5635 uu____5636
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    let uu____5649 =
      FStar_All.pipe_right flags1
        (FStar_Util.for_some
           (fun uu___81_5653  ->
              match uu___81_5653 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5654 -> false))
       in
    if uu____5649
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags1
        (FStar_List.collect
           (fun uu___82_5663  ->
              match uu___82_5663 with
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
        let uu____5682 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5682
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____5685 = destruct_comp c1  in
           match uu____5685 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____5699 =
                   let uu____5704 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____5705 =
                     let uu____5706 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____5713 =
                       let uu____5722 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____5729 =
                         let uu____5738 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____5738]  in
                       uu____5722 :: uu____5729  in
                     uu____5706 :: uu____5713  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____5704 uu____5705  in
                 uu____5699 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____5771 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t wp1 uu____5771)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5794 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____5796 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____5796
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____5799 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____5799 weaken
  
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
               let uu____5842 = destruct_comp c1  in
               match uu____5842 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____5856 =
                       let uu____5861 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____5862 =
                         let uu____5863 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____5870 =
                           let uu____5879 =
                             let uu____5886 =
                               let uu____5887 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____5887 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____5886
                              in
                           let uu____5894 =
                             let uu____5903 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____5903]  in
                           uu____5879 :: uu____5894  in
                         uu____5863 :: uu____5870  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5861 uu____5862
                        in
                     uu____5856 FStar_Pervasives_Native.None
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
            let uu____5978 = FStar_TypeChecker_Rel.is_trivial g0  in
            if uu____5978
            then (lc, g0)
            else
              (let flags1 =
                 let uu____5987 =
                   let uu____5994 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____5994
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5987 with
                 | (maybe_trivial_post,flags1) ->
                     let uu____6014 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___83_6022  ->
                               match uu___83_6022 with
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
                               | uu____6025 -> []))
                        in
                     FStar_List.append flags1 uu____6014
                  in
               let strengthen uu____6031 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____6035 = FStar_TypeChecker_Rel.guard_form g01  in
                    match uu____6035 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____6038 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____6038
                          then
                            let uu____6039 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debug_only
                               in
                            let uu____6040 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____6039 uu____6040
                          else ());
                         strengthen_comp env reason c f flags1))
                  in
               let uu____6042 =
                 let uu____6043 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____6043
                   lc.FStar_Syntax_Syntax.res_typ flags1 strengthen
                  in
               (uu____6042,
                 (let uu___111_6045 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___111_6045.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___111_6045.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___111_6045.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___84_6052  ->
            match uu___84_6052 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____6053 -> false) lc.FStar_Syntax_Syntax.cflags)
  
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
          let uu____6080 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____6080
          then e
          else
            (let uu____6084 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____6086 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____6086)
                in
             if uu____6084
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
          fun uu____6136  ->
            match uu____6136 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____6156 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____6156 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____6164 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____6164
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags1 =
                       let uu____6171 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____6171
                       then
                         let uu____6174 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____6174
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____6178 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____6178
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____6183 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____6183
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____6187 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____6187
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags1
                     else flags1)
                   in
                let bind_it uu____6196 =
                  let uu____6197 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____6197
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
                       (fun uu____6211  ->
                          let uu____6212 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____6213 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____6215 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____6212 uu____6213 uu____6215);
                     (let aux uu____6229 =
                        let uu____6230 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____6230
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____6251 ->
                              let uu____6252 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____6252
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____6271 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____6271
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let subst_c2 e1opt1 reason =
                        match (e1opt1, b) with
                        | (FStar_Pervasives_Native.Some
                           e,FStar_Pervasives_Native.Some x) ->
                            let uu____6342 =
                              let uu____6347 =
                                FStar_Syntax_Subst.subst_comp
                                  [FStar_Syntax_Syntax.NT (x, e)] c2
                                 in
                              (uu____6347, reason)  in
                            FStar_Util.Inl uu____6342
                        | uu____6354 -> aux ()  in
                      let try_simplify uu____6378 =
                        let rec maybe_close t x c =
                          let uu____6395 =
                            let uu____6396 =
                              FStar_TypeChecker_Normalize.unfold_whnf env t
                               in
                            uu____6396.FStar_Syntax_Syntax.n  in
                          match uu____6395 with
                          | FStar_Syntax_Syntax.Tm_refine (y,uu____6400) ->
                              maybe_close y.FStar_Syntax_Syntax.sort x c
                          | FStar_Syntax_Syntax.Tm_fvar fv when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.unit_lid
                              -> close_comp env [x] c
                          | uu____6406 -> c  in
                        let uu____6407 =
                          let uu____6408 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____6408  in
                        if uu____6407
                        then
                          let uu____6419 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____6419
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____6433 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____6433))
                        else
                          (let uu____6443 =
                             (FStar_Syntax_Util.is_total_comp c1) &&
                               (FStar_Syntax_Util.is_total_comp c2)
                              in
                           if uu____6443
                           then subst_c2 e1opt "both total"
                           else
                             (let uu____6453 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____6453
                              then
                                let uu____6462 =
                                  let uu____6467 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____6467, "both gtot")  in
                                FStar_Util.Inl uu____6462
                              else
                                (match (e1opt, b) with
                                 | (FStar_Pervasives_Native.Some
                                    e,FStar_Pervasives_Native.Some x) ->
                                     let uu____6499 =
                                       (FStar_Syntax_Util.is_total_comp c1)
                                         &&
                                         (let uu____6501 =
                                            FStar_Syntax_Syntax.is_null_bv x
                                             in
                                          Prims.op_Negation uu____6501)
                                        in
                                     if uu____6499
                                     then
                                       let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e)] c2
                                          in
                                       let x1 =
                                         let uu___112_6514 = x  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___112_6514.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___112_6514.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             (FStar_Syntax_Util.comp_result
                                                c1)
                                         }  in
                                       let uu____6515 =
                                         let uu____6520 =
                                           maybe_close
                                             x1.FStar_Syntax_Syntax.sort x1
                                             c21
                                            in
                                         (uu____6520, "c1 Tot")  in
                                       FStar_Util.Inl uu____6515
                                     else aux ()
                                 | uu____6526 -> aux ())))
                         in
                      let uu____6537 = try_simplify ()  in
                      match uu____6537 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____6557  ->
                                let uu____6558 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____6558);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____6567  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____6588 = lift_and_destruct env c11 c21
                                 in
                              match uu____6588 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____6641 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____6641]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____6643 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____6643]
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
                                    let uu____6670 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____6677 =
                                      let uu____6686 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____6693 =
                                        let uu____6702 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____6709 =
                                          let uu____6718 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____6725 =
                                            let uu____6734 =
                                              let uu____6741 = mk_lam wp2  in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____6741
                                               in
                                            [uu____6734]  in
                                          uu____6718 :: uu____6725  in
                                        uu____6702 :: uu____6709  in
                                      uu____6686 :: uu____6693  in
                                    uu____6670 :: uu____6677  in
                                  let wp =
                                    let uu____6781 =
                                      let uu____6786 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____6786 wp_args
                                       in
                                    uu____6781 FStar_Pervasives_Native.None
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
                              let uu____6811 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____6811 with
                              | (m,uu____6819,lift2) ->
                                  let c23 =
                                    let uu____6822 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____6822
                                     in
                                  let uu____6823 = destruct_comp c12  in
                                  (match uu____6823 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____6837 =
                                           let uu____6842 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____6843 =
                                             let uu____6844 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____6851 =
                                               let uu____6860 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____6860]  in
                                             uu____6844 :: uu____6851  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6842 uu____6843
                                            in
                                         uu____6837
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
                            let uu____6891 = destruct_comp c1_typ  in
                            match uu____6891 with
                            | (u_res_t1,res_t1,uu____6900) ->
                                let uu____6901 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____6901
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____6904 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____6904
                                   then
                                     (debug1
                                        (fun uu____6912  ->
                                           let uu____6913 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____6914 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____6913 uu____6914);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____6919 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____6921 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____6921)
                                         in
                                      if uu____6919
                                      then
                                        let e1' =
                                          let uu____6941 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____6941
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____6950  ->
                                              let uu____6951 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____6952 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____6951 uu____6952);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____6964  ->
                                              let uu____6965 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____6966 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____6965 uu____6966);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____6971 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____6971
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
      | uu____6987 -> g2
  
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
            (let uu____7009 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____7009)
           in
        let flags1 =
          if should_return1
          then
            let uu____7015 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____7015
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____7025 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____7029 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____7029
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____7031 =
              let uu____7032 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____7032  in
            (if uu____7031
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___113_7035 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___113_7035.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___113_7035.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___113_7035.FStar_Syntax_Syntax.effect_args);
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
               let uu____7046 =
                 let uu____7047 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____7047
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____7046
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____7050 =
               let uu____7051 =
                 let uu____7052 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____7052
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____7051  in
             FStar_Syntax_Util.comp_set_flags uu____7050 flags1)
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
            fun uu____7087  ->
              match uu____7087 with
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
                    let uu____7099 =
                      ((let uu____7102 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____7102) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____7099
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____7116 =
        let uu____7117 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____7117  in
      FStar_Syntax_Syntax.fvar uu____7116 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____7183  ->
                 match uu____7183 with
                 | (uu____7196,eff_label,uu____7198,uu____7199) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____7210 =
          let uu____7217 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____7251  ->
                    match uu____7251 with
                    | (uu____7264,uu____7265,flags1,uu____7267) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___85_7281  ->
                                match uu___85_7281 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____7282 -> false))))
             in
          if uu____7217
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____7210 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____7305 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____7307 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____7307
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____7341 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____7342 =
                     let uu____7347 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____7348 =
                       let uu____7349 = FStar_Syntax_Syntax.as_arg res_t1  in
                       let uu____7356 =
                         let uu____7365 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____7372 =
                           let uu____7381 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____7388 =
                             let uu____7397 = FStar_Syntax_Syntax.as_arg wp_e
                                in
                             [uu____7397]  in
                           uu____7381 :: uu____7388  in
                         uu____7365 :: uu____7372  in
                       uu____7349 :: uu____7356  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____7347 uu____7348  in
                   uu____7342 FStar_Pervasives_Native.None uu____7341  in
                 let default_case =
                   let post_k =
                     let uu____7440 =
                       let uu____7447 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____7447]  in
                     let uu____7460 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7440 uu____7460  in
                   let kwp =
                     let uu____7464 =
                       let uu____7471 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____7471]  in
                     let uu____7484 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7464 uu____7484  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____7489 =
                       let uu____7490 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____7490]  in
                     let uu____7503 =
                       let uu____7506 =
                         let uu____7513 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____7513
                          in
                       let uu____7514 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____7506 uu____7514  in
                     FStar_Syntax_Util.abs uu____7489 uu____7503
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
                   let uu____7536 =
                     should_not_inline_whole_match ||
                       (let uu____7538 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____7538)
                      in
                   if uu____7536 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____7571  ->
                        fun celse  ->
                          match uu____7571 with
                          | (g,eff_label,uu____7587,cthen) ->
                              let uu____7599 =
                                let uu____7624 =
                                  let uu____7625 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____7625
                                   in
                                lift_and_destruct env uu____7624 celse  in
                              (match uu____7599 with
                               | ((md,uu____7627,uu____7628),(uu____7629,uu____7630,wp_then),
                                  (uu____7632,uu____7633,wp_else)) ->
                                   let uu____7653 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____7653 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____7667::[] -> comp
                 | uu____7707 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____7725 = destruct_comp comp1  in
                     (match uu____7725 with
                      | (uu____7732,uu____7733,wp) ->
                          let wp1 =
                            let uu____7738 =
                              let uu____7743 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____7744 =
                                let uu____7745 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____7752 =
                                  let uu____7761 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____7761]  in
                                uu____7745 :: uu____7752  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____7743
                                uu____7744
                               in
                            uu____7738 FStar_Pervasives_Native.None
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
          let uu____7820 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____7820 with
          | FStar_Pervasives_Native.None  ->
              let uu____7829 =
                FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                  env e c c'
                 in
              let uu____7834 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____7829 uu____7834
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
            let uu____7877 =
              let uu____7878 = FStar_Syntax_Subst.compress t2  in
              uu____7878.FStar_Syntax_Syntax.n  in
            match uu____7877 with
            | FStar_Syntax_Syntax.Tm_type uu____7881 -> true
            | uu____7882 -> false  in
          let uu____7883 =
            let uu____7884 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ  in
            uu____7884.FStar_Syntax_Syntax.n  in
          match uu____7883 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____7892 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid
                 in
              let b2t1 =
                let uu____7902 =
                  FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                    e.FStar_Syntax_Syntax.pos
                   in
                FStar_Syntax_Syntax.fvar uu____7902
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None
                 in
              let lc1 =
                let uu____7904 =
                  let uu____7905 =
                    let uu____7906 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____7906
                     in
                  (FStar_Pervasives_Native.None, uu____7905)  in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____7904
                 in
              let e1 =
                let uu____7912 =
                  let uu____7917 =
                    let uu____7918 = FStar_Syntax_Syntax.as_arg e  in
                    [uu____7918]  in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____7917  in
                uu____7912 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos
                 in
              (e1, lc1)
          | uu____7939 -> (e, lc)
  
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
              (let uu____7976 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name
                  in
               match uu____7976 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____7999 -> false)
             in
          let gopt =
            if use_eq
            then
              let uu____8021 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t
                 in
              (uu____8021, false)
            else
              (let uu____8027 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____8027, true))
             in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____8038) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____8047 =
                  FStar_TypeChecker_Err.basic_type_error env
                    (FStar_Pervasives_Native.Some e) t
                    lc.FStar_Syntax_Syntax.res_typ
                   in
                FStar_Errors.raise_error uu____8047 e.FStar_Syntax_Syntax.pos
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___114_8061 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___114_8061.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___114_8061.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___114_8061.FStar_Syntax_Syntax.comp_thunk)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____8066 = FStar_TypeChecker_Rel.guard_form g  in
              (match uu____8066 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___115_8074 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___115_8074.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___115_8074.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___115_8074.FStar_Syntax_Syntax.comp_thunk)
                     }  in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___116_8077 = g  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___116_8077.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___116_8077.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___116_8077.FStar_TypeChecker_Env.implicits)
                     }  in
                   let strengthen uu____8083 =
                     let uu____8084 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ())
                        in
                     if uu____8084
                     then FStar_Syntax_Syntax.lcomp_comp lc
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f
                           in
                        let uu____8087 =
                          let uu____8088 = FStar_Syntax_Subst.compress f1  in
                          uu____8088.FStar_Syntax_Syntax.n  in
                        match uu____8087 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____8091,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____8093;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8094;_},uu____8095)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___117_8117 = lc  in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___117_8117.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___117_8117.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp_thunk =
                                  (uu___117_8117.FStar_Syntax_Syntax.comp_thunk)
                              }  in
                            FStar_Syntax_Syntax.lcomp_comp lc1
                        | uu____8118 ->
                            let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                            ((let uu____8121 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____8121
                              then
                                let uu____8122 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____8123 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t
                                   in
                                let uu____8124 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c
                                   in
                                let uu____8125 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1
                                   in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____8122 uu____8123 uu____8124 uu____8125
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
                                  let uu____8134 =
                                    let uu____8139 =
                                      let uu____8140 =
                                        FStar_Syntax_Syntax.as_arg xexp  in
                                      [uu____8140]  in
                                    FStar_Syntax_Syntax.mk_Tm_app f1
                                      uu____8139
                                     in
                                  uu____8134 FStar_Pervasives_Native.None
                                    f1.FStar_Syntax_Syntax.pos
                                else f1  in
                              let uu____8162 =
                                let uu____8167 =
                                  FStar_All.pipe_left
                                    (fun _0_17  ->
                                       FStar_Pervasives_Native.Some _0_17)
                                    (FStar_TypeChecker_Err.subtyping_failed
                                       env lc.FStar_Syntax_Syntax.res_typ t)
                                   in
                                let uu____8184 =
                                  FStar_TypeChecker_Env.set_range env
                                    e.FStar_Syntax_Syntax.pos
                                   in
                                let uu____8185 =
                                  FStar_Syntax_Util.lcomp_of_comp cret  in
                                let uu____8186 =
                                  FStar_All.pipe_left
                                    FStar_TypeChecker_Rel.guard_of_guard_formula
                                    (FStar_TypeChecker_Common.NonTrivial
                                       guard)
                                   in
                                strengthen_precondition uu____8167 uu____8184
                                  e uu____8185 uu____8186
                                 in
                              match uu____8162 with
                              | (eq_ret,_trivial_so_ok_to_discard) ->
                                  let x1 =
                                    let uu___118_8190 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___118_8190.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___118_8190.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort =
                                        (lc.FStar_Syntax_Syntax.res_typ)
                                    }  in
                                  let c1 =
                                    let uu____8192 =
                                      FStar_Syntax_Util.lcomp_of_comp c  in
                                    bind e.FStar_Syntax_Syntax.pos env
                                      (FStar_Pervasives_Native.Some e)
                                      uu____8192
                                      ((FStar_Pervasives_Native.Some x1),
                                        eq_ret)
                                     in
                                  let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                     in
                                  ((let uu____8197 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____8197
                                    then
                                      let uu____8198 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c2
                                         in
                                      FStar_Util.print1
                                        "Strengthened to %s\n" uu____8198
                                    else ());
                                   c2))))
                      in
                   let flags1 =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___86_8208  ->
                             match uu___86_8208 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____8211 -> []))
                      in
                   let lc1 =
                     let uu____8213 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name
                        in
                     FStar_Syntax_Syntax.mk_lcomp uu____8213 t flags1
                       strengthen
                      in
                   let g2 =
                     let uu___119_8215 = g1  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___119_8215.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___119_8215.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___119_8215.FStar_TypeChecker_Env.implicits)
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
        let uu____8250 =
          let uu____8251 =
            let uu____8256 =
              let uu____8257 =
                let uu____8264 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____8264  in
              [uu____8257]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____8256  in
          uu____8251 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____8250  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t
         in
      let uu____8285 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____8285
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____8301 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____8316 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____8332 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____8332
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____8346)::(ens,uu____8348)::uu____8349 ->
                    let uu____8378 =
                      let uu____8381 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____8381  in
                    let uu____8382 =
                      let uu____8383 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____8383  in
                    (uu____8378, uu____8382)
                | uu____8386 ->
                    let uu____8395 =
                      let uu____8400 =
                        let uu____8401 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____8401
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____8400)
                       in
                    FStar_Errors.raise_error uu____8395
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____8417)::uu____8418 ->
                    let uu____8437 =
                      let uu____8442 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____8442
                       in
                    (match uu____8437 with
                     | (us_r,uu____8474) ->
                         let uu____8475 =
                           let uu____8480 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____8480
                            in
                         (match uu____8475 with
                          | (us_e,uu____8512) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____8515 =
                                  let uu____8516 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8516
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8515
                                  us_r
                                 in
                              let as_ens =
                                let uu____8518 =
                                  let uu____8519 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8519
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8518
                                  us_e
                                 in
                              let req =
                                let uu____8523 =
                                  let uu____8528 =
                                    let uu____8529 =
                                      let uu____8538 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8538]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8529
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____8528
                                   in
                                uu____8523 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____8572 =
                                  let uu____8577 =
                                    let uu____8578 =
                                      let uu____8587 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8587]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8578
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____8577
                                   in
                                uu____8572 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____8618 =
                                let uu____8621 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____8621  in
                              let uu____8622 =
                                let uu____8623 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____8623  in
                              (uu____8618, uu____8622)))
                | uu____8626 -> failwith "Impossible"))
  
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
      (let uu____8656 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____8656
       then
         let uu____8657 = FStar_Syntax_Print.term_to_string tm  in
         let uu____8658 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____8657 uu____8658
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
        (let uu____8702 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____8702
         then
           let uu____8703 = FStar_Syntax_Print.term_to_string tm  in
           let uu____8704 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____8703
             uu____8704
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____8711 =
      let uu____8712 =
        let uu____8713 = FStar_Syntax_Subst.compress t  in
        uu____8713.FStar_Syntax_Syntax.n  in
      match uu____8712 with
      | FStar_Syntax_Syntax.Tm_app uu____8716 -> false
      | uu____8731 -> true  in
    if uu____8711
    then t
    else
      (let uu____8733 = FStar_Syntax_Util.head_and_args t  in
       match uu____8733 with
       | (head1,args) ->
           let uu____8770 =
             let uu____8771 =
               let uu____8772 = FStar_Syntax_Subst.compress head1  in
               uu____8772.FStar_Syntax_Syntax.n  in
             match uu____8771 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____8775 -> false  in
           if uu____8770
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____8797 ->
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
             let uu____8842 = FStar_Syntax_Util.arrow_formals t1  in
             match uu____8842 with
             | (formals,uu____8856) ->
                 let n_implicits =
                   let uu____8874 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____8952  ->
                             match uu____8952 with
                             | (uu____8959,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality))))
                      in
                   match uu____8874 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits
                    in
                 n_implicits
              in
           let inst_n_binders t1 =
             let uu____9092 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____9092 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t  in
                 let n_available = number_of_implicits t1  in
                 if n_available < n_expected
                 then
                   let uu____9116 =
                     let uu____9121 =
                       let uu____9122 = FStar_Util.string_of_int n_expected
                          in
                       let uu____9129 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____9130 = FStar_Util.string_of_int n_available
                          in
                       FStar_Util.format3
                         "Expected a term with %s implicit arguments, but %s has only %s"
                         uu____9122 uu____9129 uu____9130
                        in
                     (FStar_Errors.Fatal_MissingImplicitArguments,
                       uu____9121)
                      in
                   let uu____9137 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error uu____9116 uu____9137
                 else FStar_Pervasives_Native.Some (n_available - n_expected)
              in
           let decr_inst uu___87_9160 =
             match uu___87_9160 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
              in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____9190 = FStar_Syntax_Subst.open_comp bs c  in
               (match uu____9190 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_18,uu____9305) when
                          _0_18 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____9348,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____9381 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____9381 with
                           | (v1,uu____9421,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1  in
                               let uu____9440 =
                                 aux subst2 (decr_inst inst_n) rest  in
                               (match uu____9440 with
                                | (args,bs3,subst3,g') ->
                                    let uu____9533 =
                                      FStar_TypeChecker_Rel.conj_guard g g'
                                       in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____9533)))
                      | (uu____9560,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                       in
                    let uu____9606 =
                      let uu____9633 = inst_n_binders t  in
                      aux [] uu____9633 bs1  in
                    (match uu____9606 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____9704) -> (e, torig, guard)
                          | (uu____9735,[]) when
                              let uu____9766 =
                                FStar_Syntax_Util.is_total_comp c1  in
                              Prims.op_Negation uu____9766 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____9767 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____9795 ->
                                    FStar_Syntax_Util.arrow bs2 c1
                                 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1  in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              (e1, t2, guard))))
           | uu____9808 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____9818 =
      let uu____9821 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____9821
        (FStar_List.map
           (fun u  ->
              let uu____9831 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____9831 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____9818 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____9852 = FStar_Util.set_is_empty x  in
      if uu____9852
      then []
      else
        (let s =
           let uu____9859 =
             let uu____9862 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____9862  in
           FStar_All.pipe_right uu____9859 FStar_Util.set_elements  in
         (let uu____9870 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____9870
          then
            let uu____9871 =
              let uu____9872 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____9872  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____9871
          else ());
         (let r =
            let uu____9879 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____9879  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____9894 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____9894
                     then
                       let uu____9895 =
                         let uu____9896 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____9896
                          in
                       let uu____9897 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____9898 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____9895 uu____9897 uu____9898
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
        let uu____9924 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____9924 FStar_Util.set_elements  in
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
        | ([],uu____9962) -> generalized_univ_names
        | (uu____9969,[]) -> explicit_univ_names
        | uu____9976 ->
            let uu____9985 =
              let uu____9990 =
                let uu____9991 = FStar_Syntax_Print.term_to_string t  in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____9991
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____9990)
               in
            FStar_Errors.raise_error uu____9985 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____10009 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____10009
       then
         let uu____10010 = FStar_Syntax_Print.term_to_string t  in
         let uu____10011 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____10010 uu____10011
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____10017 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____10017
        then
          let uu____10018 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____10018
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____10024 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____10024
         then
           let uu____10025 = FStar_Syntax_Print.term_to_string t  in
           let uu____10026 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____10025 uu____10026
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
        let uu____10104 =
          let uu____10105 =
            FStar_Util.for_all
              (fun uu____10118  ->
                 match uu____10118 with
                 | (uu____10127,uu____10128,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____10105  in
        if uu____10104
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____10176 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____10176
              then
                let uu____10177 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____10177
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Exclude
                    FStar_TypeChecker_Normalize.Zeta;
                  FStar_TypeChecker_Normalize.NoFullNorm;
                  FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env c
                 in
              (let uu____10181 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____10181
               then
                 let uu____10182 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____10182
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____10197 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____10197 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____10233 =
             match uu____10233 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress
                    in
                 let c1 = norm1 c  in
                 let t1 = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t1  in
                 let uvt = FStar_Syntax_Free.uvars t1  in
                 ((let uu____10277 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____10277
                   then
                     let uu____10278 =
                       let uu____10279 =
                         let uu____10282 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____10282
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____10279
                         (FStar_String.concat ", ")
                        in
                     let uu____10325 =
                       let uu____10326 =
                         let uu____10329 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____10329
                           (FStar_List.map
                              (fun u  ->
                                 let uu____10340 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____10341 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____10340
                                   uu____10341))
                          in
                       FStar_All.pipe_right uu____10326
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____10278
                       uu____10325
                   else ());
                  (let univs2 =
                     let uu____10348 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____10360 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____10360) univs1
                       uu____10348
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____10367 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____10367
                    then
                      let uu____10368 =
                        let uu____10369 =
                          let uu____10372 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____10372
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____10369
                          (FStar_String.concat ", ")
                         in
                      let uu____10415 =
                        let uu____10416 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____10427 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____10428 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____10427
                                    uu____10428))
                           in
                        FStar_All.pipe_right uu____10416
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____10368 uu____10415
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____10442 =
             let uu____10459 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____10459  in
           match uu____10442 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____10551 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____10551
                 then ()
                 else
                   (let uu____10553 = lec_hd  in
                    match uu____10553 with
                    | (lb1,uu____10561,uu____10562) ->
                        let uu____10563 = lec2  in
                        (match uu____10563 with
                         | (lb2,uu____10571,uu____10572) ->
                             let msg =
                               let uu____10574 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10575 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____10574 uu____10575
                                in
                             let uu____10576 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____10576))
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
                 let uu____10640 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____10640
                 then ()
                 else
                   (let uu____10642 = lec_hd  in
                    match uu____10642 with
                    | (lb1,uu____10650,uu____10651) ->
                        let uu____10652 = lec2  in
                        (match uu____10652 with
                         | (lb2,uu____10660,uu____10661) ->
                             let msg =
                               let uu____10663 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10664 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____10663 uu____10664
                                in
                             let uu____10665 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____10665))
                  in
               let lecs1 =
                 let uu____10675 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____10734 = univs_and_uvars_of_lec this_lec  in
                        match uu____10734 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____10675 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____10835 = lec_hd  in
                   match uu____10835 with
                   | (lbname,e,c) ->
                       let uu____10845 =
                         let uu____10850 =
                           let uu____10851 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____10852 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____10853 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____10851 uu____10852 uu____10853
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____10850)
                          in
                       let uu____10854 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____10845 uu____10854
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____10875 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____10875 with
                         | FStar_Pervasives_Native.Some uu____10884 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____10891 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.Exclude
                                   FStar_TypeChecker_Normalize.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____10895 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____10895 with
                              | (bs,kres) ->
                                  ((let uu____10933 =
                                      let uu____10934 =
                                        let uu____10937 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____10937
                                         in
                                      uu____10934.FStar_Syntax_Syntax.n  in
                                    match uu____10933 with
                                    | FStar_Syntax_Syntax.Tm_type uu____10938
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____10942 =
                                          let uu____10943 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____10943  in
                                        if uu____10942
                                        then fail1 kres
                                        else ()
                                    | uu____10945 -> fail1 kres);
                                   (let a =
                                      let uu____10947 =
                                        let uu____10950 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _0_19  ->
                                             FStar_Pervasives_Native.Some
                                               _0_19) uu____10950
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____10947
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____10958 ->
                                          let uu____10965 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____10965
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
                      (fun uu____11076  ->
                         match uu____11076 with
                         | (lbname,e,c) ->
                             let uu____11130 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____11205 ->
                                   let uu____11220 = (e, c)  in
                                   (match uu____11220 with
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
                                                (fun uu____11271  ->
                                                   match uu____11271 with
                                                   | (x,uu____11279) ->
                                                       let uu____11284 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____11284)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____11302 =
                                                let uu____11303 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____11303
                                                 in
                                              if uu____11302
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
                                          let uu____11309 =
                                            let uu____11310 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____11310.FStar_Syntax_Syntax.n
                                             in
                                          match uu____11309 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____11331 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____11331 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____11344 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____11348 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____11348, gen_tvars))
                                in
                             (match uu____11130 with
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
        (let uu____11502 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____11502
         then
           let uu____11503 =
             let uu____11504 =
               FStar_List.map
                 (fun uu____11517  ->
                    match uu____11517 with
                    | (lb,uu____11525,uu____11526) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____11504 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____11503
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____11547  ->
                match uu____11547 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____11576 = gen env is_rec lecs  in
           match uu____11576 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____11675  ->
                       match uu____11675 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____11737 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____11737
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____11783  ->
                           match uu____11783 with
                           | (l,us,e,c,gvs) ->
                               let uu____11817 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____11818 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____11819 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____11820 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____11821 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____11817 uu____11818 uu____11819
                                 uu____11820 uu____11821))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____11862  ->
                match uu____11862 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____11906 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____11906, t, c, gvs)) univnames_lecs
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
              (let uu____11963 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____11963 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____11969 = FStar_TypeChecker_Rel.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                     uu____11969)
             in
          let is_var e1 =
            let uu____11978 =
              let uu____11979 = FStar_Syntax_Subst.compress e1  in
              uu____11979.FStar_Syntax_Syntax.n  in
            match uu____11978 with
            | FStar_Syntax_Syntax.Tm_name uu____11982 -> true
            | uu____11983 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___120_12003 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___120_12003.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___120_12003.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____12004 -> e2  in
          let env2 =
            let uu___121_12006 = env1  in
            let uu____12007 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___121_12006.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___121_12006.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___121_12006.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___121_12006.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___121_12006.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___121_12006.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___121_12006.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___121_12006.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___121_12006.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___121_12006.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___121_12006.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___121_12006.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___121_12006.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___121_12006.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___121_12006.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___121_12006.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____12007;
              FStar_TypeChecker_Env.is_iface =
                (uu___121_12006.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___121_12006.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___121_12006.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___121_12006.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___121_12006.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___121_12006.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___121_12006.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___121_12006.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___121_12006.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___121_12006.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___121_12006.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___121_12006.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___121_12006.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___121_12006.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___121_12006.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___121_12006.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___121_12006.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___121_12006.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___121_12006.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___121_12006.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___121_12006.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____12008 = check1 env2 t1 t2  in
          match uu____12008 with
          | FStar_Pervasives_Native.None  ->
              let uu____12015 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____12020 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____12015 uu____12020
          | FStar_Pervasives_Native.Some g ->
              ((let uu____12027 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12027
                then
                  let uu____12028 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____12028
                else ());
               (let uu____12030 = decorate e t2  in (uu____12030, g)))
  
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
        let uu____12062 = FStar_Syntax_Util.is_total_lcomp lc  in
        if uu____12062
        then
          let uu____12067 = discharge g1  in
          let uu____12068 = FStar_Syntax_Syntax.lcomp_comp lc  in
          (uu____12067, uu____12068)
        else
          (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
           let steps =
             [FStar_TypeChecker_Normalize.Beta;
             FStar_TypeChecker_Normalize.NoFullNorm;
             FStar_TypeChecker_Normalize.DoNotUnfoldPureLets]  in
           let c1 =
             let uu____12075 =
               let uu____12076 =
                 let uu____12077 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                 FStar_All.pipe_right uu____12077 FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____12076
                 (FStar_TypeChecker_Normalize.normalize_comp steps env)
                in
             FStar_All.pipe_right uu____12075
               (FStar_TypeChecker_Env.comp_to_comp_typ env)
              in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name
              in
           let uu____12079 = destruct_comp c1  in
           match uu____12079 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____12096 = FStar_TypeChecker_Env.get_range env  in
                 let uu____12097 =
                   let uu____12102 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial
                      in
                   let uu____12103 =
                     let uu____12104 = FStar_Syntax_Syntax.as_arg t  in
                     let uu____12111 =
                       let uu____12120 = FStar_Syntax_Syntax.as_arg wp  in
                       [uu____12120]  in
                     uu____12104 :: uu____12111  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____12102 uu____12103  in
                 uu____12097 FStar_Pervasives_Native.None uu____12096  in
               ((let uu____12148 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification")
                    in
                 if uu____12148
                 then
                   let uu____12149 = FStar_Syntax_Print.term_to_string vc  in
                   FStar_Util.print1 "top-level VC: %s\n" uu____12149
                 else ());
                (let g2 =
                   let uu____12152 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc)
                      in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____12152  in
                 let uu____12153 = discharge g2  in
                 let uu____12154 = FStar_Syntax_Syntax.mk_Comp c1  in
                 (uu____12153, uu____12154))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___88_12186 =
        match uu___88_12186 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____12194)::[] -> f fst1
        | uu____12211 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____12218 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____12218
          (fun _0_21  -> FStar_TypeChecker_Common.NonTrivial _0_21)
         in
      let op_or_e e =
        let uu____12225 =
          let uu____12226 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____12226  in
        FStar_All.pipe_right uu____12225
          (fun _0_22  -> FStar_TypeChecker_Common.NonTrivial _0_22)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_23  -> FStar_TypeChecker_Common.NonTrivial _0_23)
         in
      let op_or_t t =
        let uu____12239 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____12239
          (fun _0_24  -> FStar_TypeChecker_Common.NonTrivial _0_24)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_25  -> FStar_TypeChecker_Common.NonTrivial _0_25)
         in
      let short_op_ite uu___89_12251 =
        match uu___89_12251 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____12259)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____12278)::[] ->
            let uu____12307 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____12307
              (fun _0_26  -> FStar_TypeChecker_Common.NonTrivial _0_26)
        | uu____12308 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____12319 =
          let uu____12327 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____12327)  in
        let uu____12335 =
          let uu____12345 =
            let uu____12353 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____12353)  in
          let uu____12361 =
            let uu____12371 =
              let uu____12379 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____12379)  in
            let uu____12387 =
              let uu____12397 =
                let uu____12405 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____12405)  in
              let uu____12413 =
                let uu____12423 =
                  let uu____12431 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____12431)  in
                [uu____12423; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____12397 :: uu____12413  in
            uu____12371 :: uu____12387  in
          uu____12345 :: uu____12361  in
        uu____12319 :: uu____12335  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____12493 =
            FStar_Util.find_map table
              (fun uu____12508  ->
                 match uu____12508 with
                 | (x,mk1) ->
                     let uu____12525 = FStar_Ident.lid_equals x lid  in
                     if uu____12525
                     then
                       let uu____12528 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____12528
                     else FStar_Pervasives_Native.None)
             in
          (match uu____12493 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____12531 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____12537 =
      let uu____12538 = FStar_Syntax_Util.un_uinst l  in
      uu____12538.FStar_Syntax_Syntax.n  in
    match uu____12537 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____12542 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____12572)::uu____12573 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____12584 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____12591,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____12592))::uu____12593 -> bs
      | uu____12604 ->
          let uu____12605 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____12605 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____12609 =
                 let uu____12610 = FStar_Syntax_Subst.compress t  in
                 uu____12610.FStar_Syntax_Syntax.n  in
               (match uu____12609 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____12614) ->
                    let uu____12631 =
                      FStar_Util.prefix_until
                        (fun uu___90_12671  ->
                           match uu___90_12671 with
                           | (uu____12678,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____12679)) ->
                               false
                           | uu____12682 -> true) bs'
                       in
                    (match uu____12631 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____12717,uu____12718) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____12790,uu____12791) ->
                         let uu____12864 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____12882  ->
                                   match uu____12882 with
                                   | (x,uu____12890) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____12864
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____12933  ->
                                     match uu____12933 with
                                     | (x,i) ->
                                         let uu____12952 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____12952, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____12960 -> bs))
  
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
            let uu____12988 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____12988
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
          let uu____13015 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____13015
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
        (let uu____13050 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____13050
         then
           ((let uu____13052 = FStar_Ident.text_of_lid lident  in
             d uu____13052);
            (let uu____13053 = FStar_Ident.text_of_lid lident  in
             let uu____13054 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____13053 uu____13054))
         else ());
        (let fv =
           let uu____13057 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____13057
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
         let uu____13067 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___122_13069 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___122_13069.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___122_13069.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___122_13069.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___122_13069.FStar_Syntax_Syntax.sigattrs)
           }), uu____13067))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___91_13085 =
        match uu___91_13085 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____13086 -> false  in
      let reducibility uu___92_13092 =
        match uu___92_13092 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____13093 -> false  in
      let assumption uu___93_13099 =
        match uu___93_13099 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____13100 -> false  in
      let reification uu___94_13106 =
        match uu___94_13106 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____13107 -> true
        | uu____13108 -> false  in
      let inferred uu___95_13114 =
        match uu___95_13114 with
        | FStar_Syntax_Syntax.Discriminator uu____13115 -> true
        | FStar_Syntax_Syntax.Projector uu____13116 -> true
        | FStar_Syntax_Syntax.RecordType uu____13121 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____13130 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____13139 -> false  in
      let has_eq uu___96_13145 =
        match uu___96_13145 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____13146 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____13210 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____13215 -> true  in
      let quals = FStar_Syntax_Util.quals_of_sigelt se  in
      let uu____13219 =
        let uu____13220 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___97_13224  ->
                  match uu___97_13224 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____13225 -> false))
           in
        FStar_All.pipe_right uu____13220 Prims.op_Negation  in
      if uu____13219
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____13240 =
            let uu____13245 =
              let uu____13246 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____13246 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____13245)  in
          FStar_Errors.raise_error uu____13240 r  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____13258 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____13262 =
            let uu____13263 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____13263  in
          if uu____13262 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____13268),uu____13269) ->
              ((let uu____13279 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____13279
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____13283 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____13283
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____13289 ->
              let uu____13298 =
                let uu____13299 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x)))
                   in
                Prims.op_Negation uu____13299  in
              if uu____13298 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____13305 ->
              let uu____13312 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____13312 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____13316 ->
              let uu____13323 =
                let uu____13324 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____13324  in
              if uu____13323 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____13330 ->
              let uu____13331 =
                let uu____13332 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____13332  in
              if uu____13331 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13338 ->
              let uu____13339 =
                let uu____13340 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____13340  in
              if uu____13339 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13346 ->
              let uu____13359 =
                let uu____13360 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____13360  in
              if uu____13359 then err'1 () else ()
          | uu____13366 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec aux_whnf env t1 =
        let uu____13400 =
          let uu____13401 = FStar_Syntax_Subst.compress t1  in
          uu____13401.FStar_Syntax_Syntax.n  in
        match uu____13400 with
        | FStar_Syntax_Syntax.Tm_type uu____13404 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (let uu____13407 =
                 let uu____13412 =
                   FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
                 FStar_All.pipe_right uu____13412
                   (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
                  in
               FStar_All.pipe_right uu____13407
                 (fun l_opt  ->
                    (FStar_Util.is_some l_opt) &&
                      (let uu____13430 =
                         FStar_All.pipe_right l_opt FStar_Util.must  in
                       FStar_All.pipe_right uu____13430
                         (FStar_List.existsb
                            (fun t2  ->
                               let uu____13447 =
                                 let uu____13448 =
                                   FStar_Syntax_Subst.compress t2  in
                                 uu____13448.FStar_Syntax_Syntax.n  in
                               match uu____13447 with
                               | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                   FStar_Ident.lid_equals
                                     (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     FStar_Parser_Const.must_erase_for_extraction_attr
                                   -> true
                               | uu____13452 -> false)))))
        | FStar_Syntax_Syntax.Tm_arrow uu____13453 ->
            let uu____13466 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____13466 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____13492 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____13492
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____13494;
               FStar_Syntax_Syntax.index = uu____13495;
               FStar_Syntax_Syntax.sort = t2;_},uu____13497)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____13505,uu____13506) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____13548::[]) ->
            let uu____13579 =
              let uu____13580 = FStar_Syntax_Util.un_uinst head1  in
              uu____13580.FStar_Syntax_Syntax.n  in
            (match uu____13579 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.erased_lid
             | uu____13584 -> false)
        | uu____13585 -> false
      
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
        (let uu____13593 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____13593
         then
           let uu____13594 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____13594
         else ());
        res
       in aux g t
  