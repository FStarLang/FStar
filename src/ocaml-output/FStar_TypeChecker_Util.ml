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
                     let uu___124_241 = FStar_TypeChecker_Rel.trivial_guard
                        in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___124_241.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___124_241.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___124_241.FStar_TypeChecker_Env.univ_ineqs);
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
              ((let uu____373 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel")
                   in
                if uu____373
                then
                  let uu____374 = FStar_Syntax_Print.ctx_uvar_to_string ctx_u
                     in
                  FStar_Util.print1 "Considering closing uvar %s\n" uu____374
                else ());
               (let uu____376 =
                  FStar_Syntax_Unionfind.find
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                match uu____376 with
                | FStar_Pervasives_Native.Some uu____391 ->
                    ((let uu____393 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____393
                      then
                        let uu____394 =
                          FStar_Syntax_Print.ctx_uvar_to_string ctx_u  in
                        FStar_Util.print1
                          "%s already solved; nothing to do\n" uu____394
                      else ());
                     i)
                | FStar_Pervasives_Native.None  ->
                    let uu____396 =
                      FStar_Util.prefix_until
                        (fun uu___105_411  ->
                           match uu___105_411 with
                           | FStar_Syntax_Syntax.Binding_var uu____412 ->
                               true
                           | uu____413 -> false)
                        ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma
                       in
                    (match uu____396 with
                     | FStar_Pervasives_Native.None  -> i
                     | FStar_Pervasives_Native.Some
                         (uu____436,hd1,gamma_tail) ->
                         (FStar_TypeChecker_Common.check_uvar_ctx_invariant
                            reason range true
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders;
                          (match hd1 with
                           | FStar_Syntax_Syntax.Binding_var x' when
                               FStar_Syntax_Syntax.bv_eq x x' ->
                               let uu____471 =
                                 FStar_Util.prefix
                                   ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                  in
                               (match uu____471 with
                                | (binders_pfx,uu____503) ->
                                    let typ =
                                      let uu____527 =
                                        let uu____534 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____534]  in
                                      let uu____547 =
                                        FStar_Syntax_Syntax.mk_Total
                                          ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                         in
                                      FStar_Syntax_Util.arrow uu____527
                                        uu____547
                                       in
                                    let uu____550 =
                                      new_implicit_var_aux reason range
                                        gamma_tail binders_pfx typ
                                       in
                                    (match uu____550 with
                                     | (ctx_v,t_v) ->
                                         let sol =
                                           let uu____578 =
                                             let uu____583 =
                                               let uu____584 =
                                                 let uu____591 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     x
                                                    in
                                                 FStar_Syntax_Syntax.as_arg
                                                   uu____591
                                                  in
                                               [uu____584]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               t_v uu____583
                                              in
                                           uu____578
                                             FStar_Pervasives_Native.None
                                             range
                                            in
                                         ((let uu____607 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env)
                                               (FStar_Options.Other "Rel")
                                              in
                                           if uu____607
                                           then
                                             let uu____608 =
                                               FStar_Syntax_Print.bv_to_string
                                                 x
                                                in
                                             let uu____609 =
                                               FStar_Syntax_Print.ctx_uvar_to_string
                                                 ctx_u
                                                in
                                             let uu____610 =
                                               FStar_Syntax_Print.term_to_string
                                                 sol
                                                in
                                             FStar_Util.print3
                                               "Closing implicit %s with binder %s to %s\n"
                                               uu____608 uu____609 uu____610
                                           else ());
                                          FStar_Syntax_Unionfind.change
                                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                            sol;
                                          (reason, t_v, ctx_v, range,
                                            should_check))))
                           | uu____615 -> i)))))
           in
        let uu____616 =
          FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred
            (FStar_List.partition
               (fun uu____662  ->
                  match uu____662 with
                  | (uu____667,p) ->
                      FStar_TypeChecker_Rel.flex_prob_closing env xs p))
           in
        match uu____616 with
        | (solve_now,defer) ->
            ((let uu____696 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____696
              then
                (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                 FStar_List.iter
                   (fun uu____707  ->
                      match uu____707 with
                      | (s,p) ->
                          let uu____714 =
                            FStar_TypeChecker_Rel.prob_to_string env p  in
                          FStar_Util.print2 "%s: %s\n" s uu____714) solve_now;
                 FStar_Util.print_string " ...DEFERRED THE REST:\n";
                 FStar_List.iter
                   (fun uu____725  ->
                      match uu____725 with
                      | (s,p) ->
                          let uu____732 =
                            FStar_TypeChecker_Rel.prob_to_string env p  in
                          FStar_Util.print2 "%s: %s\n" s uu____732) defer;
                 FStar_Util.print_string "END\n")
              else ());
             (let g1 =
                FStar_TypeChecker_Rel.solve_deferred_constraints env
                  (let uu___125_736 = g  in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       (uu___125_736.FStar_TypeChecker_Env.guard_f);
                     FStar_TypeChecker_Env.deferred = solve_now;
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___125_736.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___125_736.FStar_TypeChecker_Env.implicits)
                   })
                 in
              let g2 =
                let uu___126_738 = g1  in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___126_738.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred = defer;
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___126_738.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits =
                    (uu___126_738.FStar_TypeChecker_Env.implicits)
                }  in
              (let uu____740 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____740
               then
                 let uu____741 = FStar_Syntax_Print.binders_to_string ", " xs
                    in
                 FStar_Util.print1
                   "Starting to close implicits with binders {%s}\n"
                   uu____741
               else ());
              (let is =
                 FStar_List.fold_right
                   (fun uu____781  ->
                      fun is  ->
                        match uu____781 with
                        | (x,uu____816) ->
                            ((let uu____818 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____818
                              then
                                let uu____819 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                FStar_Util.print1 "Considering closing %s\n"
                                  uu____819
                              else ());
                             FStar_List.map (aux x) is)) xs
                   g2.FStar_TypeChecker_Env.implicits
                  in
               let g3 =
                 let uu___127_846 = g2  in
                 {
                   FStar_TypeChecker_Env.guard_f =
                     (uu___127_846.FStar_TypeChecker_Env.guard_f);
                   FStar_TypeChecker_Env.deferred =
                     (uu___127_846.FStar_TypeChecker_Env.deferred);
                   FStar_TypeChecker_Env.univ_ineqs =
                     (uu___127_846.FStar_TypeChecker_Env.univ_ineqs);
                   FStar_TypeChecker_Env.implicits = is
                 }  in
               (let uu____848 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel")
                   in
                if uu____848
                then
                  let uu____849 =
                    FStar_Syntax_Print.binders_to_string ", " xs  in
                  let uu____850 =
                    FStar_TypeChecker_Rel.guard_to_string env g3  in
                  FStar_Util.print2
                    "Closed implicits with binders {%s}; guard is\n\t%s\n"
                    uu____849 uu____850
                else ());
               g3)))
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____865 =
        let uu____866 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____866  in
      if uu____865
      then
        let us =
          let uu____868 =
            let uu____871 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____871
             in
          FStar_All.pipe_right uu____868 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____882 =
            let uu____887 =
              let uu____888 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____888
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____887)  in
          FStar_Errors.log_issue r uu____882);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.typ,Prims.bool)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun uu____905  ->
      match uu____905 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____915;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____917;
          FStar_Syntax_Syntax.lbpos = uu____918;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____951 = FStar_Syntax_Subst.open_univ_vars univ_vars1 e
                  in
               (match uu____951 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____988) -> aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____995) ->
                          FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1050) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____1082 = FStar_Options.ml_ish ()  in
                                if uu____1082
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____1099 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____1099
                            then
                              let uu____1100 = FStar_Range.string_of_range r
                                 in
                              let uu____1101 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____1100 uu____1101
                            else ());
                           FStar_Util.Inl t2)
                      | uu____1103 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____1105 = aux e1  in
                      match uu____1105 with
                      | FStar_Util.Inr c ->
                          let uu____1111 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____1111
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____1113 =
                               let uu____1118 =
                                 let uu____1119 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____1119
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____1118)
                                in
                             FStar_Errors.raise_error uu____1113 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars2, t2, true))
           | uu____1123 ->
               let uu____1124 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____1124 with
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
            let uu____1218 =
              let uu____1223 =
                FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
              match uu____1223 with
              | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____1228;
                  FStar_Syntax_Syntax.vars = uu____1229;_} ->
                  let uu____1232 = FStar_Syntax_Util.type_u ()  in
                  (match uu____1232 with
                   | (t,uu____1242) ->
                       let uu____1243 =
                         let uu____1256 = FStar_Syntax_Syntax.range_of_bv x
                            in
                         new_implicit_var "pattern bv type" uu____1256 env1 t
                          in
                       (match uu____1243 with | (t1,uu____1262,g) -> (t1, g)))
              | t -> tc_annot env1 t  in
            match uu____1218 with
            | (t_x,guard) ->
                ((let uu___128_1284 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___128_1284.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___128_1284.FStar_Syntax_Syntax.index);
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
                  | uu____1359 ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant c)
                        FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                   in
                ([], [], [], env1, e, FStar_TypeChecker_Rel.trivial_guard,
                  p1)
            | FStar_Syntax_Syntax.Pat_dot_term (x,uu____1367) ->
                let uu____1372 = FStar_Syntax_Util.type_u ()  in
                (match uu____1372 with
                 | (k,uu____1398) ->
                     let uu____1399 =
                       let uu____1412 = FStar_Syntax_Syntax.range_of_bv x  in
                       new_implicit_var "pat_dot_term type" uu____1412 env1 k
                        in
                     (match uu____1399 with
                      | (t,uu____1434,g) ->
                          let x1 =
                            let uu___129_1449 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___129_1449.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___129_1449.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t
                            }  in
                          let uu____1450 =
                            let uu____1463 =
                              FStar_Syntax_Syntax.range_of_bv x1  in
                            new_implicit_var "pat_dot_term" uu____1463 env1 t
                             in
                          (match uu____1450 with
                           | (e,uu____1485,g') ->
                               let p2 =
                                 let uu___130_1502 = p1  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_dot_term
                                        (x1, e));
                                   FStar_Syntax_Syntax.p =
                                     (uu___130_1502.FStar_Syntax_Syntax.p)
                                 }  in
                               let uu____1505 =
                                 FStar_TypeChecker_Rel.conj_guard g g'  in
                               ([], [], [], env1, e, uu____1505, p2))))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let uu____1513 = check_bv env1 x  in
                (match uu____1513 with
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
                let uu____1552 = check_bv env1 x  in
                (match uu____1552 with
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
                let uu____1607 =
                  FStar_All.pipe_right pats
                    (FStar_List.fold_left
                       (fun uu____1741  ->
                          fun uu____1742  ->
                            match (uu____1741, uu____1742) with
                            | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                                let uu____1940 =
                                  pat_as_arg_with_env allow_wc_dependence
                                    env2 p2
                                   in
                                (match uu____1940 with
                                 | (b',a',w',env3,te,guard',pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te  in
                                     let uu____2016 =
                                       FStar_TypeChecker_Rel.conj_guard guard
                                         guard'
                                        in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), uu____2016, ((pat, imp)
                                       :: pats1))))
                       ([], [], [], env1, [],
                         FStar_TypeChecker_Rel.trivial_guard, []))
                   in
                (match uu____1607 with
                 | (b,a,w,env2,args,guard,pats1) ->
                     let e =
                       let uu____2147 =
                         let uu____2152 = FStar_Syntax_Syntax.fv_to_tm fv  in
                         let uu____2153 =
                           FStar_All.pipe_right args FStar_List.rev  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2152 uu____2153
                          in
                       uu____2147 FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     let uu____2170 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten
                        in
                     let uu____2181 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten
                        in
                     let uu____2192 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten
                        in
                     (uu____2170, uu____2181, uu____2192, env2, e, guard,
                       (let uu___131_2210 = p1  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___131_2210.FStar_Syntax_Syntax.p)
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
                    (fun uu____2310  ->
                       match uu____2310 with
                       | (p2,imp) ->
                           let uu____2329 = elaborate_pat env1 p2  in
                           (uu____2329, imp)) pats
                   in
                let uu____2334 =
                  FStar_TypeChecker_Env.lookup_datacon env1
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____2334 with
                 | (uu____2341,t) ->
                     let uu____2343 = FStar_Syntax_Util.arrow_formals t  in
                     (match uu____2343 with
                      | (f,uu____2359) ->
                          let rec aux formals pats2 =
                            match (formals, pats2) with
                            | ([],[]) -> []
                            | ([],uu____2485::uu____2486) ->
                                let uu____2529 =
                                  FStar_Ident.range_of_lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_TooManyPatternArguments,
                                    "Too many pattern arguments") uu____2529
                            | (uu____2538::uu____2539,[]) ->
                                FStar_All.pipe_right formals
                                  (FStar_List.map
                                     (fun uu____2617  ->
                                        match uu____2617 with
                                        | (t1,imp) ->
                                            (match imp with
                                             | FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Syntax.Implicit
                                                 inaccessible) ->
                                                 let a =
                                                   let uu____2644 =
                                                     let uu____2647 =
                                                       FStar_Syntax_Syntax.range_of_bv
                                                         t1
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____2647
                                                      in
                                                   FStar_Syntax_Syntax.new_bv
                                                     uu____2644
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let r =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 let uu____2649 =
                                                   maybe_dot inaccessible a r
                                                    in
                                                 (uu____2649, true)
                                             | uu____2654 ->
                                                 let uu____2657 =
                                                   let uu____2662 =
                                                     let uu____2663 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1
                                                        in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____2663
                                                      in
                                                   (FStar_Errors.Fatal_InsufficientPatternArguments,
                                                     uu____2662)
                                                    in
                                                 let uu____2664 =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____2657 uu____2664)))
                            | (f1::formals',(p2,p_imp)::pats') ->
                                (match f1 with
                                 | (uu____2738,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    uu____2739)) when p_imp ->
                                     let uu____2742 = aux formals' pats'  in
                                     (p2, true) :: uu____2742
                                 | (uu____2759,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    inaccessible)) ->
                                     let a =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p2.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     let p3 =
                                       let uu____2767 =
                                         FStar_Ident.range_of_lid
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          in
                                       maybe_dot inaccessible a uu____2767
                                        in
                                     let uu____2768 = aux formals' pats2  in
                                     (p3, true) :: uu____2768
                                 | (uu____2785,imp) ->
                                     let uu____2791 =
                                       let uu____2798 =
                                         FStar_Syntax_Syntax.is_implicit imp
                                          in
                                       (p2, uu____2798)  in
                                     let uu____2801 = aux formals' pats'  in
                                     uu____2791 :: uu____2801)
                             in
                          let uu___132_2816 = p1  in
                          let uu____2819 =
                            let uu____2820 =
                              let uu____2833 = aux f pats1  in
                              (fv, uu____2833)  in
                            FStar_Syntax_Syntax.Pat_cons uu____2820  in
                          {
                            FStar_Syntax_Syntax.v = uu____2819;
                            FStar_Syntax_Syntax.p =
                              (uu___132_2816.FStar_Syntax_Syntax.p)
                          }))
            | uu____2850 -> p1  in
          let one_pat allow_wc_dependence env1 p1 =
            let p2 = elaborate_pat env1 p1  in
            let uu____2892 = pat_as_arg_with_env allow_wc_dependence env1 p2
               in
            match uu____2892 with
            | (b,a,w,env2,arg,guard,p3) ->
                let uu____2950 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                   in
                (match uu____2950 with
                 | FStar_Pervasives_Native.Some x ->
                     let uu____2976 =
                       FStar_TypeChecker_Err.nonlinear_pattern_variable x  in
                     FStar_Errors.raise_error uu____2976
                       p3.FStar_Syntax_Syntax.p
                 | uu____2999 -> (b, a, w, arg, guard, p3))
             in
          let uu____3008 = one_pat true env p  in
          match uu____3008 with
          | (b,uu____3038,uu____3039,tm,guard,p1) -> (b, tm, guard, p1)
  
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
          | (uu____3101,FStar_Syntax_Syntax.Tm_uinst (e2,uu____3103)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____3108,uu____3109) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____3113 =
                    let uu____3114 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____3115 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____3114 uu____3115
                     in
                  failwith uu____3113)
               else ();
               (let uu____3118 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat")
                   in
                if uu____3118
                then
                  let uu____3119 = FStar_Syntax_Print.bv_to_string x  in
                  let uu____3120 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____3119
                    uu____3120
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___133_3124 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___133_3124.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___133_3124.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____3128 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation
                   in
                if uu____3128
                then
                  let uu____3129 =
                    let uu____3130 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____3131 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____3130 uu____3131
                     in
                  failwith uu____3129
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___134_3135 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___134_3135.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___134_3135.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____3137),uu____3138) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____3162 =
                  let uu____3163 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  Prims.op_Negation uu____3163  in
                if uu____3162
                then
                  let uu____3164 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3164
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____3183;
                FStar_Syntax_Syntax.vars = uu____3184;_},args))
              ->
              ((let uu____3223 =
                  let uu____3224 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____3224 Prims.op_Negation  in
                if uu____3223
                then
                  let uu____3225 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3225
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3363)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3438) ->
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
                       | ((e2,imp),uu____3475) ->
                           let pat =
                             let uu____3497 = aux argpat e2  in
                             let uu____3498 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3497, uu____3498)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3503 ->
                      let uu____3526 =
                        let uu____3527 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3528 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3527 uu____3528
                         in
                      failwith uu____3526
                   in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____3538;
                     FStar_Syntax_Syntax.vars = uu____3539;_},uu____3540);
                FStar_Syntax_Syntax.pos = uu____3541;
                FStar_Syntax_Syntax.vars = uu____3542;_},args))
              ->
              ((let uu____3585 =
                  let uu____3586 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____3586 Prims.op_Negation  in
                if uu____3585
                then
                  let uu____3587 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3587
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3725)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3800) ->
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
                       | ((e2,imp),uu____3837) ->
                           let pat =
                             let uu____3859 = aux argpat e2  in
                             let uu____3860 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3859, uu____3860)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3865 ->
                      let uu____3888 =
                        let uu____3889 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3890 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3889 uu____3890
                         in
                      failwith uu____3888
                   in
                match_args [] args argpats))
          | uu____3897 ->
              let uu____3902 =
                let uu____3903 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p  in
                let uu____3904 = FStar_Syntax_Print.pat_to_string qq  in
                let uu____3905 = FStar_Syntax_Print.term_to_string exp  in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____3903 uu____3904 uu____3905
                 in
              failwith uu____3902
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
    let pat_as_arg uu____3948 =
      match uu____3948 with
      | (p,i) ->
          let uu____3965 = decorated_pattern_as_term p  in
          (match uu____3965 with
           | (vars,te) ->
               let uu____3988 =
                 let uu____3993 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____3993)  in
               (vars, uu____3988))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____4007 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____4007)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____4011 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____4011)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____4015 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____4015)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____4036 =
          let uu____4053 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____4053 FStar_List.unzip  in
        (match uu____4036 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____4173 =
               let uu____4174 =
                 let uu____4175 =
                   let uu____4190 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____4190, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____4175  in
               mk1 uu____4174  in
             (vars1, uu____4173))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____4226,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____4236,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____4250 -> FStar_Pervasives_Native.Some hd1)
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____4272)::[] -> wp
      | uu____4289 ->
          let uu____4298 =
            let uu____4299 =
              let uu____4300 =
                FStar_List.map
                  (fun uu____4310  ->
                     match uu____4310 with
                     | (x,uu____4316) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____4300 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____4299
             in
          failwith uu____4298
       in
    let uu____4319 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____4319, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____4335 = destruct_comp c  in
        match uu____4335 with
        | (u,uu____4343,wp) ->
            let uu____4345 =
              let uu____4354 =
                let uu____4361 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____4361  in
              [uu____4354]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____4345;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____4389 =
          let uu____4396 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____4397 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____4396 uu____4397  in
        match uu____4389 with | (m,uu____4399,uu____4400) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____4416 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____4416
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
        let uu____4459 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____4459 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____4496 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____4496 with
             | (a,kwp) ->
                 let uu____4527 = destruct_comp m1  in
                 let uu____4534 = destruct_comp m2  in
                 ((md, a, kwp), uu____4527, uu____4534))
  
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
            let uu____4614 =
              let uu____4615 =
                let uu____4624 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____4624]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4615;
                FStar_Syntax_Syntax.flags = flags1
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4614
  
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
          let uu____4700 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____4700
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
      let uu____4712 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____4712
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____4715  ->
           let uu____4716 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____4716)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4722 =
      let uu____4723 = FStar_Syntax_Subst.compress t  in
      uu____4723.FStar_Syntax_Syntax.n  in
    match uu____4722 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4726 -> true
    | uu____4739 -> false
  
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
              let uu____4796 =
                let uu____4797 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____4797  in
              if uu____4796
              then f
              else (let uu____4799 = reason1 ()  in label uu____4799 r f)
  
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
            let uu___135_4816 = g  in
            let uu____4817 =
              let uu____4818 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____4818  in
            {
              FStar_TypeChecker_Env.guard_f = uu____4817;
              FStar_TypeChecker_Env.deferred =
                (uu___135_4816.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___135_4816.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___135_4816.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4838 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4838
        then c
        else
          (let uu____4840 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____4840
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4899 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____4899]  in
                       let us =
                         let uu____4915 =
                           let uu____4918 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____4918]  in
                         u_res :: uu____4915  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____4924 =
                         let uu____4929 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____4930 =
                           let uu____4931 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____4938 =
                             let uu____4947 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____4954 =
                               let uu____4963 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____4963]  in
                             uu____4947 :: uu____4954  in
                           uu____4931 :: uu____4938  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4929 uu____4930
                          in
                       uu____4924 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____4997 = destruct_comp c1  in
              match uu____4997 with
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
          (fun uu____5032  ->
             let uu____5033 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____5033)
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___106_5042  ->
            match uu___106_5042 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____5043 -> false))
  
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
                (let uu____5065 =
                   FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ
                    in
                 Prims.op_Negation uu____5065))
               &&
               (let uu____5072 = FStar_Syntax_Util.head_and_args' e  in
                match uu____5072 with
                | (head1,uu____5086) ->
                    let uu____5103 =
                      let uu____5104 = FStar_Syntax_Util.un_uinst head1  in
                      uu____5104.FStar_Syntax_Syntax.n  in
                    (match uu____5103 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____5108 =
                           let uu____5109 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____5109
                            in
                         Prims.op_Negation uu____5108
                     | uu____5110 -> true)))
              &&
              (let uu____5112 = should_not_inline_lc lc  in
               Prims.op_Negation uu____5112)
  
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
            let uu____5146 =
              let uu____5147 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____5147  in
            if uu____5146
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____5149 = FStar_Syntax_Util.is_unit t  in
               if uu____5149
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
                    let uu____5155 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____5155
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____5157 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____5157 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____5167 =
                             let uu____5168 =
                               let uu____5173 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____5174 =
                                 let uu____5175 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____5182 =
                                   let uu____5191 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____5191]  in
                                 uu____5175 :: uu____5182  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____5173
                                 uu____5174
                                in
                             uu____5168 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.NoFullNorm] env
                             uu____5167)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____5219 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____5219
           then
             let uu____5220 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____5221 = FStar_Syntax_Print.term_to_string v1  in
             let uu____5222 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____5220 uu____5221 uu____5222
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    let uu____5235 =
      FStar_All.pipe_right flags1
        (FStar_Util.for_some
           (fun uu___107_5239  ->
              match uu___107_5239 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5240 -> false))
       in
    if uu____5235
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags1
        (FStar_List.collect
           (fun uu___108_5249  ->
              match uu___108_5249 with
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
        let uu____5268 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5268
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____5271 = destruct_comp c1  in
           match uu____5271 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____5285 =
                   let uu____5290 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____5291 =
                     let uu____5292 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____5299 =
                       let uu____5308 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____5315 =
                         let uu____5324 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____5324]  in
                       uu____5308 :: uu____5315  in
                     uu____5292 :: uu____5299  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____5290 uu____5291  in
                 uu____5285 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____5357 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t wp1 uu____5357)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5380 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____5382 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____5382
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____5385 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____5385 weaken
  
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
               let uu____5428 = destruct_comp c1  in
               match uu____5428 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____5442 =
                       let uu____5447 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____5448 =
                         let uu____5449 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____5456 =
                           let uu____5465 =
                             let uu____5472 =
                               let uu____5473 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____5473 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____5472
                              in
                           let uu____5480 =
                             let uu____5489 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____5489]  in
                           uu____5465 :: uu____5480  in
                         uu____5449 :: uu____5456  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5447 uu____5448
                        in
                     uu____5442 FStar_Pervasives_Native.None
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
            let uu____5564 = FStar_TypeChecker_Rel.is_trivial g0  in
            if uu____5564
            then (lc, g0)
            else
              (let flags1 =
                 let uu____5573 =
                   let uu____5580 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____5580
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5573 with
                 | (maybe_trivial_post,flags1) ->
                     let uu____5600 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___109_5608  ->
                               match uu___109_5608 with
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
                               | uu____5611 -> []))
                        in
                     FStar_List.append flags1 uu____5600
                  in
               let strengthen uu____5617 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____5621 = FStar_TypeChecker_Rel.guard_form g01  in
                    match uu____5621 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____5624 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____5624
                          then
                            let uu____5625 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debug_only
                               in
                            let uu____5626 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____5625 uu____5626
                          else ());
                         strengthen_comp env reason c f flags1))
                  in
               let uu____5628 =
                 let uu____5629 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____5629
                   lc.FStar_Syntax_Syntax.res_typ flags1 strengthen
                  in
               (uu____5628,
                 (let uu___136_5631 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___136_5631.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___136_5631.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___136_5631.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___110_5638  ->
            match uu___110_5638 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____5639 -> false) lc.FStar_Syntax_Syntax.cflags)
  
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
          let uu____5666 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____5666
          then e
          else
            (let uu____5670 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____5672 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____5672)
                in
             if uu____5670
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
          fun uu____5722  ->
            match uu____5722 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____5742 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____5742 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____5750 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____5750
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags1 =
                       let uu____5757 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____5757
                       then
                         let uu____5760 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____5760
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5764 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____5764
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5769 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____5769
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____5773 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____5773
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags1
                     else flags1)
                   in
                let bind_it uu____5782 =
                  let uu____5783 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____5783
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
                       (fun uu____5797  ->
                          let uu____5798 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____5799 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____5801 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____5798 uu____5799 uu____5801);
                     (let aux uu____5815 =
                        let uu____5816 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____5816
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____5837 ->
                              let uu____5838 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____5838
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____5857 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____5857
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let subst_c2 e1opt1 reason =
                        match (e1opt1, b) with
                        | (FStar_Pervasives_Native.Some
                           e,FStar_Pervasives_Native.Some x) ->
                            let uu____5928 =
                              let uu____5933 =
                                FStar_Syntax_Subst.subst_comp
                                  [FStar_Syntax_Syntax.NT (x, e)] c2
                                 in
                              (uu____5933, reason)  in
                            FStar_Util.Inl uu____5928
                        | uu____5940 -> aux ()  in
                      let try_simplify uu____5964 =
                        let rec maybe_close t x c =
                          let uu____5981 =
                            let uu____5982 =
                              FStar_TypeChecker_Normalize.unfold_whnf env t
                               in
                            uu____5982.FStar_Syntax_Syntax.n  in
                          match uu____5981 with
                          | FStar_Syntax_Syntax.Tm_refine (y,uu____5986) ->
                              maybe_close y.FStar_Syntax_Syntax.sort x c
                          | FStar_Syntax_Syntax.Tm_fvar fv when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.unit_lid
                              -> close_comp env [x] c
                          | uu____5992 -> c  in
                        let uu____5993 =
                          let uu____5994 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____5994  in
                        if uu____5993
                        then
                          let uu____6005 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____6005
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____6019 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____6019))
                        else
                          (let uu____6029 =
                             (FStar_Syntax_Util.is_total_comp c1) &&
                               (FStar_Syntax_Util.is_total_comp c2)
                              in
                           if uu____6029
                           then subst_c2 e1opt "both total"
                           else
                             (let uu____6039 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____6039
                              then
                                let uu____6048 =
                                  let uu____6053 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____6053, "both gtot")  in
                                FStar_Util.Inl uu____6048
                              else
                                (match (e1opt, b) with
                                 | (FStar_Pervasives_Native.Some
                                    e,FStar_Pervasives_Native.Some x) ->
                                     let uu____6077 =
                                       (FStar_Syntax_Util.is_total_comp c1)
                                         &&
                                         (let uu____6079 =
                                            FStar_Syntax_Syntax.is_null_bv x
                                             in
                                          Prims.op_Negation uu____6079)
                                        in
                                     if uu____6077
                                     then
                                       let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e)] c2
                                          in
                                       let x1 =
                                         let uu___137_6092 = x  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___137_6092.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___137_6092.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             (FStar_Syntax_Util.comp_result
                                                c1)
                                         }  in
                                       let uu____6093 =
                                         let uu____6098 =
                                           maybe_close
                                             x1.FStar_Syntax_Syntax.sort x1
                                             c21
                                            in
                                         (uu____6098, "c1 Tot")  in
                                       FStar_Util.Inl uu____6093
                                     else aux ()
                                 | uu____6104 -> aux ())))
                         in
                      let uu____6113 = try_simplify ()  in
                      match uu____6113 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____6133  ->
                                let uu____6134 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____6134);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____6143  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____6164 = lift_and_destruct env c11 c21
                                 in
                              match uu____6164 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____6217 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____6217]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____6231 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____6231]
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
                                    let uu____6258 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____6265 =
                                      let uu____6274 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____6281 =
                                        let uu____6290 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____6297 =
                                          let uu____6306 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____6313 =
                                            let uu____6322 =
                                              let uu____6329 = mk_lam wp2  in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____6329
                                               in
                                            [uu____6322]  in
                                          uu____6306 :: uu____6313  in
                                        uu____6290 :: uu____6297  in
                                      uu____6274 :: uu____6281  in
                                    uu____6258 :: uu____6265  in
                                  let wp =
                                    let uu____6369 =
                                      let uu____6374 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____6374 wp_args
                                       in
                                    uu____6369 FStar_Pervasives_Native.None
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
                              let uu____6399 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____6399 with
                              | (m,uu____6407,lift2) ->
                                  let c23 =
                                    let uu____6410 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____6410
                                     in
                                  let uu____6411 = destruct_comp c12  in
                                  (match uu____6411 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____6425 =
                                           let uu____6430 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____6431 =
                                             let uu____6432 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____6439 =
                                               let uu____6448 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____6448]  in
                                             uu____6432 :: uu____6439  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6430 uu____6431
                                            in
                                         uu____6425
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
                            let uu____6479 = destruct_comp c1_typ  in
                            match uu____6479 with
                            | (u_res_t1,res_t1,uu____6488) ->
                                let uu____6489 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____6489
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____6492 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____6492
                                   then
                                     (debug1
                                        (fun uu____6500  ->
                                           let uu____6501 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____6502 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____6501 uu____6502);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____6507 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____6509 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____6509)
                                         in
                                      if uu____6507
                                      then
                                        let e1' =
                                          let uu____6529 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____6529
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____6538  ->
                                              let uu____6539 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____6540 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____6539 uu____6540);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____6552  ->
                                              let uu____6553 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____6554 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____6553 uu____6554);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____6559 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____6559
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
      | uu____6575 -> g2
  
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
            (let uu____6597 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____6597)
           in
        let flags1 =
          if should_return1
          then
            let uu____6603 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____6603
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____6615 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____6619 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____6619
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____6623 =
              let uu____6624 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____6624  in
            (if uu____6623
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___138_6629 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___138_6629.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___138_6629.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___138_6629.FStar_Syntax_Syntax.effect_args);
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
               let uu____6640 =
                 let uu____6641 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____6641
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6640
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____6644 =
               let uu____6645 =
                 let uu____6646 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____6646
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____6645  in
             FStar_Syntax_Util.comp_set_flags uu____6644 flags1)
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
            fun uu____6681  ->
              match uu____6681 with
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
                    let uu____6693 =
                      ((let uu____6696 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____6696) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____6693
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6710 =
        let uu____6711 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6711  in
      FStar_Syntax_Syntax.fvar uu____6710 FStar_Syntax_Syntax.delta_constant
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
               fun uu____6777  ->
                 match uu____6777 with
                 | (uu____6790,eff_label,uu____6792,uu____6793) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____6804 =
          let uu____6811 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____6845  ->
                    match uu____6845 with
                    | (uu____6858,uu____6859,flags1,uu____6861) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___111_6875  ->
                                match uu___111_6875 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____6876 -> false))))
             in
          if uu____6811
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____6804 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____6899 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____6901 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____6901
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____6939 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____6940 =
                     let uu____6945 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____6946 =
                       let uu____6947 = FStar_Syntax_Syntax.as_arg res_t1  in
                       let uu____6954 =
                         let uu____6963 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____6970 =
                           let uu____6979 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____6986 =
                             let uu____6995 = FStar_Syntax_Syntax.as_arg wp_e
                                in
                             [uu____6995]  in
                           uu____6979 :: uu____6986  in
                         uu____6963 :: uu____6970  in
                       uu____6947 :: uu____6954  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____6945 uu____6946  in
                   uu____6940 FStar_Pervasives_Native.None uu____6939  in
                 let default_case =
                   let post_k =
                     let uu____7038 =
                       let uu____7045 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____7045]  in
                     let uu____7058 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7038 uu____7058  in
                   let kwp =
                     let uu____7064 =
                       let uu____7071 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____7071]  in
                     let uu____7084 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7064 uu____7084  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____7091 =
                       let uu____7092 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____7092]  in
                     let uu____7105 =
                       let uu____7108 =
                         let uu____7115 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____7115
                          in
                       let uu____7116 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____7108 uu____7116  in
                     FStar_Syntax_Util.abs uu____7091 uu____7105
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
                   let uu____7138 =
                     should_not_inline_whole_match ||
                       (let uu____7140 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____7140)
                      in
                   if uu____7138 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____7173  ->
                        fun celse  ->
                          match uu____7173 with
                          | (g,eff_label,uu____7189,cthen) ->
                              let uu____7201 =
                                let uu____7226 =
                                  let uu____7227 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____7227
                                   in
                                lift_and_destruct env uu____7226 celse  in
                              (match uu____7201 with
                               | ((md,uu____7229,uu____7230),(uu____7231,uu____7232,wp_then),
                                  (uu____7234,uu____7235,wp_else)) ->
                                   let uu____7255 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____7255 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____7269::[] -> comp
                 | uu____7309 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____7327 = destruct_comp comp1  in
                     (match uu____7327 with
                      | (uu____7334,uu____7335,wp) ->
                          let wp1 =
                            let uu____7340 =
                              let uu____7345 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____7346 =
                                let uu____7347 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____7354 =
                                  let uu____7363 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____7363]  in
                                uu____7347 :: uu____7354  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____7345
                                uu____7346
                               in
                            uu____7340 FStar_Pervasives_Native.None
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
          let uu____7422 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____7422 with
          | FStar_Pervasives_Native.None  ->
              let uu____7431 =
                FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                  env e c c'
                 in
              let uu____7436 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____7431 uu____7436
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
            let uu____7479 =
              let uu____7480 = FStar_Syntax_Subst.compress t2  in
              uu____7480.FStar_Syntax_Syntax.n  in
            match uu____7479 with
            | FStar_Syntax_Syntax.Tm_type uu____7483 -> true
            | uu____7484 -> false  in
          let uu____7485 =
            let uu____7486 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ  in
            uu____7486.FStar_Syntax_Syntax.n  in
          match uu____7485 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____7494 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid
                 in
              let b2t1 =
                let uu____7504 =
                  FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                    e.FStar_Syntax_Syntax.pos
                   in
                FStar_Syntax_Syntax.fvar uu____7504
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None
                 in
              let lc1 =
                let uu____7506 =
                  let uu____7507 =
                    let uu____7508 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____7508
                     in
                  (FStar_Pervasives_Native.None, uu____7507)  in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____7506
                 in
              let e1 =
                let uu____7514 =
                  let uu____7519 =
                    let uu____7520 = FStar_Syntax_Syntax.as_arg e  in
                    [uu____7520]  in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____7519  in
                uu____7514 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos
                 in
              (e1, lc1)
          | uu____7541 -> (e, lc)
  
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
              (let uu____7578 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name
                  in
               match uu____7578 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____7601 -> false)
             in
          let gopt =
            if use_eq
            then
              let uu____7623 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t
                 in
              (uu____7623, false)
            else
              (let uu____7629 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____7629, true))
             in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____7640) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____7649 =
                  FStar_TypeChecker_Err.basic_type_error env
                    (FStar_Pervasives_Native.Some e) t
                    lc.FStar_Syntax_Syntax.res_typ
                   in
                FStar_Errors.raise_error uu____7649 e.FStar_Syntax_Syntax.pos
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___139_7663 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___139_7663.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___139_7663.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___139_7663.FStar_Syntax_Syntax.comp_thunk)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____7668 = FStar_TypeChecker_Rel.guard_form g  in
              (match uu____7668 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___140_7676 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___140_7676.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___140_7676.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___140_7676.FStar_Syntax_Syntax.comp_thunk)
                     }  in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___141_7679 = g  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___141_7679.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___141_7679.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___141_7679.FStar_TypeChecker_Env.implicits)
                     }  in
                   let strengthen uu____7685 =
                     let uu____7686 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ())
                        in
                     if uu____7686
                     then FStar_Syntax_Syntax.lcomp_comp lc
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f
                           in
                        let uu____7689 =
                          let uu____7690 = FStar_Syntax_Subst.compress f1  in
                          uu____7690.FStar_Syntax_Syntax.n  in
                        match uu____7689 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____7693,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____7695;
                                          FStar_Syntax_Syntax.vars =
                                            uu____7696;_},uu____7697)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___142_7719 = lc  in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___142_7719.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___142_7719.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp_thunk =
                                  (uu___142_7719.FStar_Syntax_Syntax.comp_thunk)
                              }  in
                            FStar_Syntax_Syntax.lcomp_comp lc1
                        | uu____7720 ->
                            let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                            ((let uu____7723 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____7723
                              then
                                let uu____7724 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____7725 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t
                                   in
                                let uu____7726 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c
                                   in
                                let uu____7727 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1
                                   in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____7724 uu____7725 uu____7726 uu____7727
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
                                  let uu____7736 =
                                    let uu____7741 =
                                      let uu____7742 =
                                        FStar_Syntax_Syntax.as_arg xexp  in
                                      [uu____7742]  in
                                    FStar_Syntax_Syntax.mk_Tm_app f1
                                      uu____7741
                                     in
                                  uu____7736 FStar_Pervasives_Native.None
                                    f1.FStar_Syntax_Syntax.pos
                                else f1  in
                              let uu____7764 =
                                let uu____7769 =
                                  FStar_All.pipe_left
                                    (fun _0_17  ->
                                       FStar_Pervasives_Native.Some _0_17)
                                    (FStar_TypeChecker_Err.subtyping_failed
                                       env lc.FStar_Syntax_Syntax.res_typ t)
                                   in
                                let uu____7786 =
                                  FStar_TypeChecker_Env.set_range env
                                    e.FStar_Syntax_Syntax.pos
                                   in
                                let uu____7787 =
                                  FStar_Syntax_Util.lcomp_of_comp cret  in
                                let uu____7788 =
                                  FStar_All.pipe_left
                                    FStar_TypeChecker_Rel.guard_of_guard_formula
                                    (FStar_TypeChecker_Common.NonTrivial
                                       guard)
                                   in
                                strengthen_precondition uu____7769 uu____7786
                                  e uu____7787 uu____7788
                                 in
                              match uu____7764 with
                              | (eq_ret,_trivial_so_ok_to_discard) ->
                                  let x1 =
                                    let uu___143_7792 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___143_7792.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___143_7792.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort =
                                        (lc.FStar_Syntax_Syntax.res_typ)
                                    }  in
                                  let c1 =
                                    let uu____7794 =
                                      FStar_Syntax_Util.lcomp_of_comp c  in
                                    bind e.FStar_Syntax_Syntax.pos env
                                      (FStar_Pervasives_Native.Some e)
                                      uu____7794
                                      ((FStar_Pervasives_Native.Some x1),
                                        eq_ret)
                                     in
                                  let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                     in
                                  ((let uu____7799 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____7799
                                    then
                                      let uu____7800 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c2
                                         in
                                      FStar_Util.print1
                                        "Strengthened to %s\n" uu____7800
                                    else ());
                                   c2))))
                      in
                   let flags1 =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___112_7810  ->
                             match uu___112_7810 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____7813 -> []))
                      in
                   let lc1 =
                     let uu____7815 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name
                        in
                     FStar_Syntax_Syntax.mk_lcomp uu____7815 t flags1
                       strengthen
                      in
                   let g2 =
                     let uu___144_7817 = g1  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___144_7817.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___144_7817.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___144_7817.FStar_TypeChecker_Env.implicits)
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
        let uu____7852 =
          let uu____7855 =
            let uu____7860 =
              let uu____7861 =
                let uu____7868 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____7868  in
              [uu____7861]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____7860  in
          uu____7855 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____7852  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t
         in
      let uu____7889 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____7889
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____7905 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____7920 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____7936 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____7936
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____7950)::(ens,uu____7952)::uu____7953 ->
                    let uu____7982 =
                      let uu____7985 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____7985  in
                    let uu____7986 =
                      let uu____7987 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____7987  in
                    (uu____7982, uu____7986)
                | uu____7990 ->
                    let uu____7999 =
                      let uu____8004 =
                        let uu____8005 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____8005
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____8004)
                       in
                    FStar_Errors.raise_error uu____7999
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____8021)::uu____8022 ->
                    let uu____8041 =
                      let uu____8046 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____8046
                       in
                    (match uu____8041 with
                     | (us_r,uu____8078) ->
                         let uu____8079 =
                           let uu____8084 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____8084
                            in
                         (match uu____8079 with
                          | (us_e,uu____8116) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____8119 =
                                  let uu____8120 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8120
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8119
                                  us_r
                                 in
                              let as_ens =
                                let uu____8122 =
                                  let uu____8123 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8123
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8122
                                  us_e
                                 in
                              let req =
                                let uu____8127 =
                                  let uu____8132 =
                                    let uu____8133 =
                                      let uu____8142 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8142]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8133
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____8132
                                   in
                                uu____8127 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____8174 =
                                  let uu____8179 =
                                    let uu____8180 =
                                      let uu____8189 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8189]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8180
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____8179
                                   in
                                uu____8174 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____8218 =
                                let uu____8221 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____8221  in
                              let uu____8222 =
                                let uu____8223 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____8223  in
                              (uu____8218, uu____8222)))
                | uu____8226 -> failwith "Impossible"))
  
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
      (let uu____8256 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____8256
       then
         let uu____8257 = FStar_Syntax_Print.term_to_string tm  in
         let uu____8258 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____8257 uu____8258
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
        (let uu____8302 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____8302
         then
           let uu____8303 = FStar_Syntax_Print.term_to_string tm  in
           let uu____8304 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____8303
             uu____8304
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____8311 =
      let uu____8312 =
        let uu____8313 = FStar_Syntax_Subst.compress t  in
        uu____8313.FStar_Syntax_Syntax.n  in
      match uu____8312 with
      | FStar_Syntax_Syntax.Tm_app uu____8316 -> false
      | uu____8331 -> true  in
    if uu____8311
    then t
    else
      (let uu____8333 = FStar_Syntax_Util.head_and_args t  in
       match uu____8333 with
       | (head1,args) ->
           let uu____8370 =
             let uu____8371 =
               let uu____8372 = FStar_Syntax_Subst.compress head1  in
               uu____8372.FStar_Syntax_Syntax.n  in
             match uu____8371 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____8375 -> false  in
           if uu____8370
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____8397 ->
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
             let uu____8442 = FStar_Syntax_Util.arrow_formals t1  in
             match uu____8442 with
             | (formals,uu____8456) ->
                 let n_implicits =
                   let uu____8474 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____8552  ->
                             match uu____8552 with
                             | (uu____8559,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality))))
                      in
                   match uu____8474 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits
                    in
                 n_implicits
              in
           let inst_n_binders t1 =
             let uu____8692 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____8692 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t  in
                 let n_available = number_of_implicits t1  in
                 if n_available < n_expected
                 then
                   let uu____8716 =
                     let uu____8721 =
                       let uu____8722 = FStar_Util.string_of_int n_expected
                          in
                       let uu____8729 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____8730 = FStar_Util.string_of_int n_available
                          in
                       FStar_Util.format3
                         "Expected a term with %s implicit arguments, but %s has only %s"
                         uu____8722 uu____8729 uu____8730
                        in
                     (FStar_Errors.Fatal_MissingImplicitArguments,
                       uu____8721)
                      in
                   let uu____8737 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error uu____8716 uu____8737
                 else FStar_Pervasives_Native.Some (n_available - n_expected)
              in
           let decr_inst uu___113_8760 =
             match uu___113_8760 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
              in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____8790 = FStar_Syntax_Subst.open_comp bs c  in
               (match uu____8790 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_18,uu____8905) when
                          _0_18 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____8948,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____8981 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____8981 with
                           | (v1,uu____9021,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1  in
                               let uu____9040 =
                                 aux subst2 (decr_inst inst_n) rest  in
                               (match uu____9040 with
                                | (args,bs3,subst3,g') ->
                                    let uu____9133 =
                                      FStar_TypeChecker_Rel.conj_guard g g'
                                       in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____9133)))
                      | (uu____9160,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                       in
                    let uu____9206 =
                      let uu____9233 = inst_n_binders t  in
                      aux [] uu____9233 bs1  in
                    (match uu____9206 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____9304) -> (e, torig, guard)
                          | (uu____9335,[]) when
                              let uu____9366 =
                                FStar_Syntax_Util.is_total_comp c1  in
                              Prims.op_Negation uu____9366 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____9367 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____9395 ->
                                    FStar_Syntax_Util.arrow bs2 c1
                                 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1  in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              (e1, t2, guard))))
           | uu____9408 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____9418 =
      let uu____9421 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____9421
        (FStar_List.map
           (fun u  ->
              let uu____9431 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____9431 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____9418 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____9452 = FStar_Util.set_is_empty x  in
      if uu____9452
      then []
      else
        (let s =
           let uu____9467 =
             let uu____9470 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____9470  in
           FStar_All.pipe_right uu____9467 FStar_Util.set_elements  in
         (let uu____9486 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____9486
          then
            let uu____9487 =
              let uu____9488 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____9488  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____9487
          else ());
         (let r =
            let uu____9495 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____9495  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____9534 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____9534
                     then
                       let uu____9535 =
                         let uu____9536 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____9536
                          in
                       let uu____9537 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____9538 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____9535 uu____9537 uu____9538
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
        let uu____9564 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____9564 FStar_Util.set_elements  in
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
        | ([],uu____9602) -> generalized_univ_names
        | (uu____9609,[]) -> explicit_univ_names
        | uu____9616 ->
            let uu____9625 =
              let uu____9630 =
                let uu____9631 = FStar_Syntax_Print.term_to_string t  in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____9631
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____9630)
               in
            FStar_Errors.raise_error uu____9625 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____9649 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____9649
       then
         let uu____9650 = FStar_Syntax_Print.term_to_string t  in
         let uu____9651 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____9650 uu____9651
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____9657 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____9657
        then
          let uu____9658 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____9658
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____9664 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____9664
         then
           let uu____9665 = FStar_Syntax_Print.term_to_string t  in
           let uu____9666 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____9665 uu____9666
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
        let uu____9744 =
          let uu____9745 =
            FStar_Util.for_all
              (fun uu____9758  ->
                 match uu____9758 with
                 | (uu____9767,uu____9768,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____9745  in
        if uu____9744
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____9816 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____9816
              then
                let uu____9817 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____9817
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Exclude
                    FStar_TypeChecker_Normalize.Zeta;
                  FStar_TypeChecker_Normalize.NoFullNorm;
                  FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env c
                 in
              (let uu____9821 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____9821
               then
                 let uu____9822 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____9822
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____9837 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____9837 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____9873 =
             match uu____9873 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress
                    in
                 let c1 = norm1 c  in
                 let t1 = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t1  in
                 let uvt = FStar_Syntax_Free.uvars t1  in
                 ((let uu____9917 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____9917
                   then
                     let uu____9918 =
                       let uu____9919 =
                         let uu____9922 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____9922
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____9919
                         (FStar_String.concat ", ")
                        in
                     let uu____9965 =
                       let uu____9966 =
                         let uu____9969 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____9969
                           (FStar_List.map
                              (fun u  ->
                                 let uu____9980 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____9981 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____9980
                                   uu____9981))
                          in
                       FStar_All.pipe_right uu____9966
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____9918
                       uu____9965
                   else ());
                  (let univs2 =
                     let uu____9988 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____10000 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____10000) univs1
                       uu____9988
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____10007 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____10007
                    then
                      let uu____10008 =
                        let uu____10009 =
                          let uu____10012 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____10012
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____10009
                          (FStar_String.concat ", ")
                         in
                      let uu____10055 =
                        let uu____10056 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____10067 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____10068 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____10067
                                    uu____10068))
                           in
                        FStar_All.pipe_right uu____10056
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____10008 uu____10055
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____10082 =
             let uu____10099 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____10099  in
           match uu____10082 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____10191 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____10191
                 then ()
                 else
                   (let uu____10193 = lec_hd  in
                    match uu____10193 with
                    | (lb1,uu____10201,uu____10202) ->
                        let uu____10203 = lec2  in
                        (match uu____10203 with
                         | (lb2,uu____10211,uu____10212) ->
                             let msg =
                               let uu____10214 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10215 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____10214 uu____10215
                                in
                             let uu____10216 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____10216))
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
                 let uu____10280 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____10280
                 then ()
                 else
                   (let uu____10282 = lec_hd  in
                    match uu____10282 with
                    | (lb1,uu____10290,uu____10291) ->
                        let uu____10292 = lec2  in
                        (match uu____10292 with
                         | (lb2,uu____10300,uu____10301) ->
                             let msg =
                               let uu____10303 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10304 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____10303 uu____10304
                                in
                             let uu____10305 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____10305))
                  in
               let lecs1 =
                 let uu____10315 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____10374 = univs_and_uvars_of_lec this_lec  in
                        match uu____10374 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____10315 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____10475 = lec_hd  in
                   match uu____10475 with
                   | (lbname,e,c) ->
                       let uu____10485 =
                         let uu____10490 =
                           let uu____10491 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____10492 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____10493 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____10491 uu____10492 uu____10493
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____10490)
                          in
                       let uu____10494 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____10485 uu____10494
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____10515 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____10515 with
                         | FStar_Pervasives_Native.Some uu____10524 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____10531 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.Exclude
                                   FStar_TypeChecker_Normalize.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____10535 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____10535 with
                              | (bs,kres) ->
                                  ((let uu____10573 =
                                      let uu____10574 =
                                        let uu____10577 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____10577
                                         in
                                      uu____10574.FStar_Syntax_Syntax.n  in
                                    match uu____10573 with
                                    | FStar_Syntax_Syntax.Tm_type uu____10578
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____10582 =
                                          let uu____10583 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____10583  in
                                        if uu____10582
                                        then fail1 kres
                                        else ()
                                    | uu____10585 -> fail1 kres);
                                   (let a =
                                      let uu____10587 =
                                        let uu____10590 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _0_19  ->
                                             FStar_Pervasives_Native.Some
                                               _0_19) uu____10590
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____10587
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____10598 ->
                                          let uu____10605 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____10605
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
                      (fun uu____10716  ->
                         match uu____10716 with
                         | (lbname,e,c) ->
                             let uu____10770 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____10845 ->
                                   let uu____10860 = (e, c)  in
                                   (match uu____10860 with
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
                                                (fun uu____10911  ->
                                                   match uu____10911 with
                                                   | (x,uu____10919) ->
                                                       let uu____10924 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____10924)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____10942 =
                                                let uu____10943 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____10943
                                                 in
                                              if uu____10942
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
                                          let uu____10949 =
                                            let uu____10950 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____10950.FStar_Syntax_Syntax.n
                                             in
                                          match uu____10949 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____10971 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____10971 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____10984 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____10988 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____10988, gen_tvars))
                                in
                             (match uu____10770 with
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
        (let uu____11142 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____11142
         then
           let uu____11143 =
             let uu____11144 =
               FStar_List.map
                 (fun uu____11157  ->
                    match uu____11157 with
                    | (lb,uu____11165,uu____11166) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____11144 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____11143
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____11187  ->
                match uu____11187 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____11216 = gen env is_rec lecs  in
           match uu____11216 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____11315  ->
                       match uu____11315 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____11377 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____11377
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____11423  ->
                           match uu____11423 with
                           | (l,us,e,c,gvs) ->
                               let uu____11457 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____11458 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____11459 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____11460 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____11461 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____11457 uu____11458 uu____11459
                                 uu____11460 uu____11461))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____11502  ->
                match uu____11502 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____11546 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____11546, t, c, gvs)) univnames_lecs
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
              (let uu____11603 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____11603 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____11609 = FStar_TypeChecker_Rel.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                     uu____11609)
             in
          let is_var e1 =
            let uu____11618 =
              let uu____11619 = FStar_Syntax_Subst.compress e1  in
              uu____11619.FStar_Syntax_Syntax.n  in
            match uu____11618 with
            | FStar_Syntax_Syntax.Tm_name uu____11622 -> true
            | uu____11623 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___145_11643 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___145_11643.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___145_11643.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____11644 -> e2  in
          let env2 =
            let uu___146_11646 = env1  in
            let uu____11647 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___146_11646.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___146_11646.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___146_11646.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___146_11646.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___146_11646.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___146_11646.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___146_11646.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___146_11646.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___146_11646.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___146_11646.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___146_11646.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___146_11646.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___146_11646.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___146_11646.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___146_11646.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___146_11646.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____11647;
              FStar_TypeChecker_Env.is_iface =
                (uu___146_11646.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___146_11646.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___146_11646.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___146_11646.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___146_11646.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___146_11646.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___146_11646.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___146_11646.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___146_11646.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___146_11646.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___146_11646.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___146_11646.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___146_11646.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___146_11646.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___146_11646.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___146_11646.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___146_11646.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___146_11646.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___146_11646.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___146_11646.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___146_11646.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____11648 = check1 env2 t1 t2  in
          match uu____11648 with
          | FStar_Pervasives_Native.None  ->
              let uu____11655 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____11660 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____11655 uu____11660
          | FStar_Pervasives_Native.Some g ->
              ((let uu____11667 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____11667
                then
                  let uu____11668 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____11668
                else ());
               (let uu____11670 = decorate e t2  in (uu____11670, g)))
  
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
        let uu____11702 = FStar_Syntax_Util.is_total_lcomp lc  in
        if uu____11702
        then
          let uu____11707 = discharge g1  in
          let uu____11708 = FStar_Syntax_Syntax.lcomp_comp lc  in
          (uu____11707, uu____11708)
        else
          (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
           let steps =
             [FStar_TypeChecker_Normalize.Beta;
             FStar_TypeChecker_Normalize.NoFullNorm;
             FStar_TypeChecker_Normalize.DoNotUnfoldPureLets]  in
           let c1 =
             let uu____11715 =
               let uu____11716 =
                 let uu____11717 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                 FStar_All.pipe_right uu____11717 FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____11716
                 (FStar_TypeChecker_Normalize.normalize_comp steps env)
                in
             FStar_All.pipe_right uu____11715
               (FStar_TypeChecker_Env.comp_to_comp_typ env)
              in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name
              in
           let uu____11719 = destruct_comp c1  in
           match uu____11719 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____11736 = FStar_TypeChecker_Env.get_range env  in
                 let uu____11737 =
                   let uu____11742 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial
                      in
                   let uu____11743 =
                     let uu____11744 = FStar_Syntax_Syntax.as_arg t  in
                     let uu____11751 =
                       let uu____11760 = FStar_Syntax_Syntax.as_arg wp  in
                       [uu____11760]  in
                     uu____11744 :: uu____11751  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____11742 uu____11743  in
                 uu____11737 FStar_Pervasives_Native.None uu____11736  in
               ((let uu____11788 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification")
                    in
                 if uu____11788
                 then
                   let uu____11789 = FStar_Syntax_Print.term_to_string vc  in
                   FStar_Util.print1 "top-level VC: %s\n" uu____11789
                 else ());
                (let g2 =
                   let uu____11792 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc)
                      in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____11792  in
                 let uu____11793 = discharge g2  in
                 let uu____11794 = FStar_Syntax_Syntax.mk_Comp c1  in
                 (uu____11793, uu____11794))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___114_11826 =
        match uu___114_11826 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____11834)::[] -> f fst1
        | uu____11851 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____11862 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____11862
          (fun _0_21  -> FStar_TypeChecker_Common.NonTrivial _0_21)
         in
      let op_or_e e =
        let uu____11873 =
          let uu____11874 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____11874  in
        FStar_All.pipe_right uu____11873
          (fun _0_22  -> FStar_TypeChecker_Common.NonTrivial _0_22)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_23  -> FStar_TypeChecker_Common.NonTrivial _0_23)
         in
      let op_or_t t =
        let uu____11893 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____11893
          (fun _0_24  -> FStar_TypeChecker_Common.NonTrivial _0_24)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_25  -> FStar_TypeChecker_Common.NonTrivial _0_25)
         in
      let short_op_ite uu___115_11907 =
        match uu___115_11907 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____11915)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____11934)::[] ->
            let uu____11963 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____11963
              (fun _0_26  -> FStar_TypeChecker_Common.NonTrivial _0_26)
        | uu____11964 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____11975 =
          let uu____11983 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____11983)  in
        let uu____11991 =
          let uu____12001 =
            let uu____12009 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____12009)  in
          let uu____12017 =
            let uu____12027 =
              let uu____12035 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____12035)  in
            let uu____12043 =
              let uu____12053 =
                let uu____12061 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____12061)  in
              let uu____12069 =
                let uu____12079 =
                  let uu____12087 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____12087)  in
                [uu____12079; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____12053 :: uu____12069  in
            uu____12027 :: uu____12043  in
          uu____12001 :: uu____12017  in
        uu____11975 :: uu____11991  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____12149 =
            FStar_Util.find_map table
              (fun uu____12164  ->
                 match uu____12164 with
                 | (x,mk1) ->
                     let uu____12181 = FStar_Ident.lid_equals x lid  in
                     if uu____12181
                     then
                       let uu____12184 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____12184
                     else FStar_Pervasives_Native.None)
             in
          (match uu____12149 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____12187 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____12193 =
      let uu____12194 = FStar_Syntax_Util.un_uinst l  in
      uu____12194.FStar_Syntax_Syntax.n  in
    match uu____12193 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____12198 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____12228)::uu____12229 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____12240 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____12247,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____12248))::uu____12249 -> bs
      | uu____12260 ->
          let uu____12261 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____12261 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____12265 =
                 let uu____12266 = FStar_Syntax_Subst.compress t  in
                 uu____12266.FStar_Syntax_Syntax.n  in
               (match uu____12265 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____12270) ->
                    let uu____12287 =
                      FStar_Util.prefix_until
                        (fun uu___116_12327  ->
                           match uu___116_12327 with
                           | (uu____12334,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____12335)) ->
                               false
                           | uu____12338 -> true) bs'
                       in
                    (match uu____12287 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____12373,uu____12374) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____12446,uu____12447) ->
                         let uu____12520 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____12538  ->
                                   match uu____12538 with
                                   | (x,uu____12546) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____12520
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____12589  ->
                                     match uu____12589 with
                                     | (x,i) ->
                                         let uu____12608 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____12608, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____12616 -> bs))
  
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
            let uu____12644 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____12644
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
          let uu____12671 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____12671
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
        (let uu____12706 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____12706
         then
           ((let uu____12708 = FStar_Ident.text_of_lid lident  in
             d uu____12708);
            (let uu____12709 = FStar_Ident.text_of_lid lident  in
             let uu____12710 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____12709 uu____12710))
         else ());
        (let fv =
           let uu____12713 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____12713
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
         let uu____12723 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___147_12725 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___147_12725.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___147_12725.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___147_12725.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___147_12725.FStar_Syntax_Syntax.sigattrs)
           }), uu____12723))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___117_12741 =
        match uu___117_12741 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____12742 -> false  in
      let reducibility uu___118_12748 =
        match uu___118_12748 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____12749 -> false  in
      let assumption uu___119_12755 =
        match uu___119_12755 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____12756 -> false  in
      let reification uu___120_12762 =
        match uu___120_12762 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____12763 -> true
        | uu____12764 -> false  in
      let inferred uu___121_12770 =
        match uu___121_12770 with
        | FStar_Syntax_Syntax.Discriminator uu____12771 -> true
        | FStar_Syntax_Syntax.Projector uu____12772 -> true
        | FStar_Syntax_Syntax.RecordType uu____12777 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____12786 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____12795 -> false  in
      let has_eq uu___122_12801 =
        match uu___122_12801 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____12802 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____12866 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____12871 -> true  in
      let quals = FStar_Syntax_Util.quals_of_sigelt se  in
      let uu____12875 =
        let uu____12876 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___123_12880  ->
                  match uu___123_12880 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____12881 -> false))
           in
        FStar_All.pipe_right uu____12876 Prims.op_Negation  in
      if uu____12875
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____12896 =
            let uu____12901 =
              let uu____12902 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____12902 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____12901)  in
          FStar_Errors.raise_error uu____12896 r  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____12914 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____12918 =
            let uu____12919 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____12919  in
          if uu____12918 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____12924),uu____12925) ->
              ((let uu____12935 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____12935
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____12939 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____12939
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____12945 ->
              let uu____12954 =
                let uu____12955 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x)))
                   in
                Prims.op_Negation uu____12955  in
              if uu____12954 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____12961 ->
              let uu____12968 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____12968 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____12972 ->
              let uu____12979 =
                let uu____12980 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____12980  in
              if uu____12979 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____12986 ->
              let uu____12987 =
                let uu____12988 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____12988  in
              if uu____12987 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12994 ->
              let uu____12995 =
                let uu____12996 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____12996  in
              if uu____12995 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13002 ->
              let uu____13015 =
                let uu____13016 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____13016  in
              if uu____13015 then err'1 () else ()
          | uu____13022 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec aux_whnf env t1 =
        let uu____13056 =
          let uu____13057 = FStar_Syntax_Subst.compress t1  in
          uu____13057.FStar_Syntax_Syntax.n  in
        match uu____13056 with
        | FStar_Syntax_Syntax.Tm_type uu____13060 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (let uu____13063 =
                 let uu____13068 =
                   FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
                 FStar_All.pipe_right uu____13068
                   (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
                  in
               FStar_All.pipe_right uu____13063
                 (fun l_opt  ->
                    (FStar_Util.is_some l_opt) &&
                      (let uu____13086 =
                         FStar_All.pipe_right l_opt FStar_Util.must  in
                       FStar_All.pipe_right uu____13086
                         (FStar_List.existsb
                            (fun t2  ->
                               let uu____13103 =
                                 let uu____13104 =
                                   FStar_Syntax_Subst.compress t2  in
                                 uu____13104.FStar_Syntax_Syntax.n  in
                               match uu____13103 with
                               | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                   FStar_Ident.lid_equals
                                     (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     FStar_Parser_Const.must_erase_for_extraction_attr
                                   -> true
                               | uu____13108 -> false)))))
        | FStar_Syntax_Syntax.Tm_arrow uu____13109 ->
            let uu____13122 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____13122 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____13148 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____13148
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____13150;
               FStar_Syntax_Syntax.index = uu____13151;
               FStar_Syntax_Syntax.sort = t2;_},uu____13153)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____13161,uu____13162) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____13204::[]) ->
            let uu____13235 =
              let uu____13236 = FStar_Syntax_Util.un_uinst head1  in
              uu____13236.FStar_Syntax_Syntax.n  in
            (match uu____13235 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.erased_lid
             | uu____13240 -> false)
        | uu____13241 -> false
      
      and aux env t1 =
        let t2 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Primops;
            FStar_TypeChecker_Normalize.Weak;
            FStar_TypeChecker_Normalize.HNF;
            FStar_TypeChecker_Normalize.UnfoldUntil
              FStar_Syntax_Syntax.delta_constant;
            FStar_TypeChecker_Normalize.Beta;
            FStar_TypeChecker_Normalize.AllowUnboundUniverses;
            FStar_TypeChecker_Normalize.Zeta;
            FStar_TypeChecker_Normalize.Iota] env t1
           in
        let res = aux_whnf env t2  in
        (let uu____13249 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____13249
         then
           let uu____13250 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____13250
         else ());
        res
       in aux g t
  