open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option *
    FStar_TypeChecker_Common.lcomp)
let (report : FStar_TypeChecker_Env.env -> Prims.string Prims.list -> unit) =
  fun env ->
    fun errs ->
      let uu____22 = FStar_TypeChecker_Env.get_range env in
      let uu____23 = FStar_TypeChecker_Err.failed_to_prove_specification errs in
      FStar_Errors.log_issue uu____22 uu____23
let (new_implicit_var :
  Prims.string ->
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.ctx_uvar *
            FStar_Range.range) Prims.list * FStar_TypeChecker_Common.guard_t))
  =
  fun reason ->
    fun r ->
      fun env ->
        fun k ->
          FStar_TypeChecker_Env.new_implicit_var_aux reason r env k
            FStar_Syntax_Syntax.Strict FStar_Pervasives_Native.None
let (close_guard_implicits :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      FStar_Syntax_Syntax.binders ->
        FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun solve_deferred ->
      fun xs ->
        fun g ->
          let uu____87 = (FStar_Options.eager_subtyping ()) || solve_deferred in
          if uu____87
          then
            let uu____90 =
              FStar_All.pipe_right g.FStar_TypeChecker_Common.deferred
                (FStar_List.partition
                   (fun uu____142 ->
                      match uu____142 with
                      | (uu____149, p) ->
                          FStar_TypeChecker_Rel.flex_prob_closing env xs p)) in
            match uu____90 with
            | (solve_now, defer) ->
                ((let uu____184 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel") in
                  if uu____184
                  then
                    (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                     FStar_List.iter
                       (fun uu____201 ->
                          match uu____201 with
                          | (s, p) ->
                              let uu____211 =
                                FStar_TypeChecker_Rel.prob_to_string env p in
                              FStar_Util.print2 "%s: %s\n" s uu____211)
                       solve_now;
                     FStar_Util.print_string " ...DEFERRED THE REST:\n";
                     FStar_List.iter
                       (fun uu____226 ->
                          match uu____226 with
                          | (s, p) ->
                              let uu____236 =
                                FStar_TypeChecker_Rel.prob_to_string env p in
                              FStar_Util.print2 "%s: %s\n" s uu____236) defer;
                     FStar_Util.print_string "END\n")
                  else ());
                 (let g1 =
                    FStar_TypeChecker_Rel.solve_deferred_constraints env
                      (let uu___49_244 = g in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___49_244.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred_to_tac =
                           (uu___49_244.FStar_TypeChecker_Common.deferred_to_tac);
                         FStar_TypeChecker_Common.deferred = solve_now;
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___49_244.FStar_TypeChecker_Common.univ_ineqs);
                         FStar_TypeChecker_Common.implicits =
                           (uu___49_244.FStar_TypeChecker_Common.implicits)
                       }) in
                  let g2 =
                    let uu___52_246 = g1 in
                    {
                      FStar_TypeChecker_Common.guard_f =
                        (uu___52_246.FStar_TypeChecker_Common.guard_f);
                      FStar_TypeChecker_Common.deferred_to_tac =
                        (uu___52_246.FStar_TypeChecker_Common.deferred_to_tac);
                      FStar_TypeChecker_Common.deferred = defer;
                      FStar_TypeChecker_Common.univ_ineqs =
                        (uu___52_246.FStar_TypeChecker_Common.univ_ineqs);
                      FStar_TypeChecker_Common.implicits =
                        (uu___52_246.FStar_TypeChecker_Common.implicits)
                    } in
                  g2))
          else g
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r ->
    fun t ->
      let uvs = FStar_Syntax_Free.uvars t in
      let uu____263 =
        let uu____265 = FStar_Util.set_is_empty uvs in
        Prims.op_Negation uu____265 in
      if uu____263
      then
        let us =
          let uu____270 =
            let uu____274 = FStar_Util.set_elements uvs in
            FStar_List.map
              (fun u ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____274 in
          FStar_All.pipe_right uu____270 (FStar_String.concat ", ") in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____293 =
            let uu____299 =
              let uu____301 = FStar_Syntax_Print.term_to_string t in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____301 in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____299) in
          FStar_Errors.log_issue r uu____293);
         FStar_Options.pop ())
      else ()
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool))
  =
  fun env ->
    fun uu____324 ->
      match uu____324 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____335;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____337;
          FStar_Syntax_Syntax.lbpos = uu____338;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname in
          let t1 = FStar_Syntax_Subst.compress t in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown ->
               let uu____373 = FStar_Syntax_Subst.open_univ_vars univ_vars e in
               (match uu____373 with
                | (univ_vars1, e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                    let r = FStar_TypeChecker_Env.get_range env1 in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2 in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4, uu____411) -> aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4, t2, uu____418)
                          -> FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs, body, uu____473) ->
                          let res = aux body in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____509 = FStar_Options.ml_ish () in
                                if uu____509
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              c.FStar_Syntax_Syntax.pos in
                          ((let uu____531 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High in
                            if uu____531
                            then
                              let uu____534 = FStar_Range.string_of_range r in
                              let uu____536 =
                                FStar_Syntax_Print.term_to_string t2 in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____534 uu____536
                            else ());
                           FStar_Util.Inl t2)
                      | uu____541 -> FStar_Util.Inl FStar_Syntax_Syntax.tun in
                    let t2 =
                      let uu____543 = aux e1 in
                      match uu____543 with
                      | FStar_Util.Inr c ->
                          let uu____549 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c in
                          if uu____549
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____554 =
                               let uu____560 =
                                 let uu____562 =
                                   FStar_Syntax_Print.comp_to_string c in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____562 in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____560) in
                             FStar_Errors.raise_error uu____554 rng)
                      | FStar_Util.Inl t2 -> t2 in
                    (univ_vars1, t2, true))
           | uu____571 ->
               let uu____572 = FStar_Syntax_Subst.open_univ_vars univ_vars t1 in
               (match uu____572 with
                | (univ_vars1, t2) -> (univ_vars1, t2, false)))
let rec (decorated_pattern_as_term :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun pat ->
    let mk f = FStar_Syntax_Syntax.mk f pat.FStar_Syntax_Syntax.p in
    let pat_as_arg uu____636 =
      match uu____636 with
      | (p, i) ->
          let uu____656 = decorated_pattern_as_term p in
          (match uu____656 with
           | (vars, te) ->
               let uu____679 =
                 let uu____684 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____684) in
               (vars, uu____679)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____698 = mk (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____698)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____702 = mk (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____702)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____706 = mk (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____706)
    | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
        let uu____729 =
          let uu____748 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____748 FStar_List.unzip in
        (match uu____729 with
         | (vars, args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____886 =
               let uu____887 =
                 let uu____888 =
                   let uu____905 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____905, args) in
                 FStar_Syntax_Syntax.Tm_app uu____888 in
               mk uu____887 in
             (vars1, uu____886))
    | FStar_Syntax_Syntax.Pat_dot_term (x, e) -> ([], e)
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____944, uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____954, uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd::uu____968 -> FStar_Pervasives_Native.Some hd)
let (lcomp_univ_opt :
  FStar_TypeChecker_Common.lcomp ->
    (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option *
      FStar_TypeChecker_Common.guard_t))
  =
  fun lc ->
    let uu____983 =
      FStar_All.pipe_right lc FStar_TypeChecker_Common.lcomp_comp in
    FStar_All.pipe_right uu____983
      (fun uu____1011 ->
         match uu____1011 with | (c, g) -> ((comp_univ_opt c), g))
let (destruct_wp_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  = fun c -> FStar_Syntax_Util.destruct_comp c
let (mk_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname ->
    fun u_result ->
      fun result ->
        fun wp ->
          fun flags ->
            let uu____1084 =
              let uu____1085 =
                let uu____1096 = FStar_Syntax_Syntax.as_arg wp in
                [uu____1096] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____1085;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____1084
let (mk_comp :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  = fun md -> mk_comp_l md.FStar_Syntax_Syntax.mname
let (effect_args_from_repr :
  FStar_Syntax_Syntax.term ->
    Prims.bool -> FStar_Range.range -> FStar_Syntax_Syntax.term Prims.list)
  =
  fun repr ->
    fun is_layered ->
      fun r ->
        let err uu____1180 =
          let uu____1181 =
            let uu____1187 =
              let uu____1189 = FStar_Syntax_Print.term_to_string repr in
              let uu____1191 = FStar_Util.string_of_bool is_layered in
              FStar_Util.format2
                "Could not get effect args from repr %s with is_layered %s"
                uu____1189 uu____1191 in
            (FStar_Errors.Fatal_UnexpectedEffect, uu____1187) in
          FStar_Errors.raise_error uu____1181 r in
        let repr1 = FStar_Syntax_Subst.compress repr in
        if is_layered
        then
          match repr1.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_app (uu____1203, uu____1204::is) ->
              FStar_All.pipe_right is
                (FStar_List.map FStar_Pervasives_Native.fst)
          | uu____1272 -> err ()
        else
          (match repr1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (uu____1277, c) ->
               let uu____1299 =
                 FStar_All.pipe_right c FStar_Syntax_Util.comp_to_comp_typ in
               FStar_All.pipe_right uu____1299
                 (fun ct ->
                    FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                      (FStar_List.map FStar_Pervasives_Native.fst))
           | uu____1334 -> err ())
let (mk_wp_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term ->
            FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun ed ->
      fun u_a ->
        fun a ->
          fun e ->
            fun r ->
              let c =
                let uu____1367 =
                  let uu____1369 =
                    FStar_TypeChecker_Env.lid_exists env
                      FStar_Parser_Const.effect_GTot_lid in
                  FStar_All.pipe_left Prims.op_Negation uu____1369 in
                if uu____1367
                then FStar_Syntax_Syntax.mk_Total a
                else
                  (let uu____1376 = FStar_Syntax_Util.is_unit a in
                   if uu____1376
                   then
                     FStar_Syntax_Syntax.mk_Total' a
                       (FStar_Pervasives_Native.Some
                          FStar_Syntax_Syntax.U_zero)
                   else
                     (let wp =
                        let uu____1382 =
                          env.FStar_TypeChecker_Env.lax &&
                            (FStar_Options.ml_ish ()) in
                        if uu____1382
                        then FStar_Syntax_Syntax.tun
                        else
                          (let ret_wp =
                             FStar_All.pipe_right ed
                               FStar_Syntax_Util.get_return_vc_combinator in
                           let uu____1388 =
                             let uu____1389 =
                               FStar_TypeChecker_Env.inst_effect_fun_with
                                 [u_a] env ed ret_wp in
                             let uu____1390 =
                               let uu____1391 = FStar_Syntax_Syntax.as_arg a in
                               let uu____1400 =
                                 let uu____1411 =
                                   FStar_Syntax_Syntax.as_arg e in
                                 [uu____1411] in
                               uu____1391 :: uu____1400 in
                             FStar_Syntax_Syntax.mk_Tm_app uu____1389
                               uu____1390 e.FStar_Syntax_Syntax.pos in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____1388) in
                      mk_comp ed u_a a wp [FStar_Syntax_Syntax.RETURN])) in
              (let uu____1445 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Return") in
               if uu____1445
               then
                 let uu____1450 =
                   FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                 let uu____1452 = FStar_Syntax_Print.term_to_string e in
                 let uu____1454 =
                   FStar_TypeChecker_Normalize.comp_to_string env c in
                 FStar_Util.print3 "(%s) returning %s at comp type %s\n"
                   uu____1450 uu____1452 uu____1454
               else ());
              c
let (mk_indexed_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term ->
            FStar_Range.range ->
              (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun ed ->
      fun u_a ->
        fun a ->
          fun e ->
            fun r ->
              (let uu____1499 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "LayeredEffects") in
               if uu____1499
               then
                 let uu____1504 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                 let uu____1506 = FStar_Syntax_Print.univ_to_string u_a in
                 let uu____1508 = FStar_Syntax_Print.term_to_string a in
                 let uu____1510 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print4
                   "Computing %s.return for u_a:%s, a:%s, and e:%s{\n"
                   uu____1504 uu____1506 uu____1508 uu____1510
               else ());
              (let uu____1515 =
                 let uu____1520 =
                   FStar_All.pipe_right ed
                     FStar_Syntax_Util.get_return_vc_combinator in
                 FStar_TypeChecker_Env.inst_tscheme_with uu____1520 [u_a] in
               match uu____1515 with
               | (uu____1525, return_t) ->
                   let return_t_shape_error s =
                     let uu____1540 =
                       let uu____1542 =
                         FStar_Ident.string_of_lid
                           ed.FStar_Syntax_Syntax.mname in
                       let uu____1544 =
                         FStar_Syntax_Print.term_to_string return_t in
                       FStar_Util.format3
                         "%s.return %s does not have proper shape (reason:%s)"
                         uu____1542 uu____1544 s in
                     (FStar_Errors.Fatal_UnexpectedEffect, uu____1540) in
                   let uu____1548 =
                     let uu____1577 =
                       let uu____1578 = FStar_Syntax_Subst.compress return_t in
                       uu____1578.FStar_Syntax_Syntax.n in
                     match uu____1577 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                         (FStar_List.length bs) >= (Prims.of_int (2)) ->
                         let uu____1638 = FStar_Syntax_Subst.open_comp bs c in
                         (match uu____1638 with
                          | (a_b::x_b::bs1, c1) ->
                              let uu____1707 =
                                FStar_Syntax_Util.comp_to_comp_typ c1 in
                              (a_b, x_b, bs1, uu____1707))
                     | uu____1728 ->
                         let uu____1729 =
                           return_t_shape_error
                             "Either not an arrow or not enough binders" in
                         FStar_Errors.raise_error uu____1729 r in
                   (match uu____1548 with
                    | (a_b, x_b, rest_bs, return_ct) ->
                        let uu____1812 =
                          let uu____1819 =
                            let uu____1820 =
                              let uu____1821 =
                                let uu____1828 =
                                  FStar_All.pipe_right a_b
                                    FStar_Pervasives_Native.fst in
                                (uu____1828, a) in
                              FStar_Syntax_Syntax.NT uu____1821 in
                            let uu____1839 =
                              let uu____1842 =
                                let uu____1843 =
                                  let uu____1850 =
                                    FStar_All.pipe_right x_b
                                      FStar_Pervasives_Native.fst in
                                  (uu____1850, e) in
                                FStar_Syntax_Syntax.NT uu____1843 in
                              [uu____1842] in
                            uu____1820 :: uu____1839 in
                          FStar_TypeChecker_Env.uvars_for_binders env rest_bs
                            uu____1819
                            (fun b ->
                               let uu____1866 =
                                 FStar_Syntax_Print.binder_to_string b in
                               let uu____1868 =
                                 let uu____1870 =
                                   FStar_Ident.string_of_lid
                                     ed.FStar_Syntax_Syntax.mname in
                                 FStar_Util.format1 "%s.return" uu____1870 in
                               let uu____1873 = FStar_Range.string_of_range r in
                               FStar_Util.format3
                                 "implicit var for binder %s of %s at %s"
                                 uu____1866 uu____1868 uu____1873) r in
                        (match uu____1812 with
                         | (rest_bs_uvars, g_uvars) ->
                             let subst =
                               FStar_List.map2
                                 (fun b ->
                                    fun t ->
                                      let uu____1910 =
                                        let uu____1917 =
                                          FStar_All.pipe_right b
                                            FStar_Pervasives_Native.fst in
                                        (uu____1917, t) in
                                      FStar_Syntax_Syntax.NT uu____1910) (a_b
                                 :: x_b :: rest_bs) (a :: e :: rest_bs_uvars) in
                             let is =
                               let uu____1943 =
                                 let uu____1946 =
                                   FStar_Syntax_Subst.compress
                                     return_ct.FStar_Syntax_Syntax.result_typ in
                                 let uu____1947 =
                                   FStar_Syntax_Util.is_layered ed in
                                 effect_args_from_repr uu____1946 uu____1947
                                   r in
                               FStar_All.pipe_right uu____1943
                                 (FStar_List.map
                                    (FStar_Syntax_Subst.subst subst)) in
                             let c =
                               let uu____1954 =
                                 let uu____1955 =
                                   FStar_All.pipe_right is
                                     (FStar_List.map
                                        FStar_Syntax_Syntax.as_arg) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs = [u_a];
                                   FStar_Syntax_Syntax.effect_name =
                                     (ed.FStar_Syntax_Syntax.mname);
                                   FStar_Syntax_Syntax.result_typ = a;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____1955;
                                   FStar_Syntax_Syntax.flags = []
                                 } in
                               FStar_Syntax_Syntax.mk_Comp uu____1954 in
                             ((let uu____1979 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffects") in
                               if uu____1979
                               then
                                 let uu____1984 =
                                   FStar_Syntax_Print.comp_to_string c in
                                 FStar_Util.print1 "} c after return %s\n"
                                   uu____1984
                               else ());
                              (c, g_uvars)))))
let (mk_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term ->
            FStar_Range.range ->
              (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun ed ->
      fun u_a ->
        fun a ->
          fun e ->
            fun r ->
              let uu____2028 =
                FStar_All.pipe_right ed FStar_Syntax_Util.is_layered in
              if uu____2028
              then mk_indexed_return env ed u_a a e r
              else
                (let uu____2038 = mk_wp_return env ed u_a a e r in
                 (uu____2038, FStar_TypeChecker_Env.trivial_guard))
let (lift_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp_typ ->
      FStar_TypeChecker_Env.mlift ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun c ->
      fun lift ->
        let uu____2063 =
          FStar_All.pipe_right
            (let uu___257_2065 = c in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___257_2065.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___257_2065.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ =
                 (uu___257_2065.FStar_Syntax_Syntax.result_typ);
               FStar_Syntax_Syntax.effect_args =
                 (uu___257_2065.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags = []
             }) FStar_Syntax_Syntax.mk_Comp in
        FStar_All.pipe_right uu____2063
          (lift.FStar_TypeChecker_Env.mlift_wp env)
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env ->
    fun l1_in ->
      fun l2_in ->
        let uu____2086 =
          let uu____2091 = FStar_TypeChecker_Env.norm_eff_name env l1_in in
          let uu____2092 = FStar_TypeChecker_Env.norm_eff_name env l2_in in
          (uu____2091, uu____2092) in
        match uu____2086 with
        | (l1, l2) ->
            let uu____2095 = FStar_TypeChecker_Env.join_opt env l1 l2 in
            (match uu____2095 with
             | FStar_Pervasives_Native.Some (m, uu____2105, uu____2106) -> m
             | FStar_Pervasives_Native.None ->
                 let uu____2119 =
                   FStar_TypeChecker_Env.exists_polymonadic_bind env l1 l2 in
                 (match uu____2119 with
                  | FStar_Pervasives_Native.Some (m, uu____2133) -> m
                  | FStar_Pervasives_Native.None ->
                      let uu____2166 =
                        let uu____2172 =
                          let uu____2174 =
                            FStar_Syntax_Print.lid_to_string l1_in in
                          let uu____2176 =
                            FStar_Syntax_Print.lid_to_string l2_in in
                          FStar_Util.format2
                            "Effects %s and %s cannot be composed" uu____2174
                            uu____2176 in
                        (FStar_Errors.Fatal_EffectsCannotBeComposed,
                          uu____2172) in
                      FStar_Errors.raise_error uu____2166
                        env.FStar_TypeChecker_Env.range))
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env ->
    fun c1 ->
      fun c2 ->
        let uu____2196 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2) in
        if uu____2196
        then FStar_Parser_Const.effect_Tot_lid
        else
          join_effects env c1.FStar_TypeChecker_Common.eff_name
            c2.FStar_TypeChecker_Common.eff_name
let (lift_comps_sep_guards :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
          Prims.bool ->
            (FStar_Ident.lident * FStar_Syntax_Syntax.comp *
              FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t *
              FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun c1 ->
      fun c2 ->
        fun b ->
          fun for_bind ->
            let c11 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1 in
            let c21 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2 in
            let uu____2255 =
              FStar_TypeChecker_Env.join_opt env
                c11.FStar_Syntax_Syntax.effect_name
                c21.FStar_Syntax_Syntax.effect_name in
            match uu____2255 with
            | FStar_Pervasives_Native.Some (m, lift1, lift2) ->
                let uu____2283 = lift_comp env c11 lift1 in
                (match uu____2283 with
                 | (c12, g1) ->
                     let uu____2300 =
                       if Prims.op_Negation for_bind
                       then lift_comp env c21 lift2
                       else
                         (let x_a =
                            match b with
                            | FStar_Pervasives_Native.None ->
                                FStar_Syntax_Syntax.null_binder
                                  (FStar_Syntax_Util.comp_result c12)
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Syntax.mk_binder x in
                          let env_x =
                            FStar_TypeChecker_Env.push_binders env [x_a] in
                          let uu____2339 = lift_comp env_x c21 lift2 in
                          match uu____2339 with
                          | (c22, g2) ->
                              let uu____2350 =
                                FStar_TypeChecker_Env.close_guard env 
                                  [x_a] g2 in
                              (c22, uu____2350)) in
                     (match uu____2300 with
                      | (c22, g2) -> (m, c12, c22, g1, g2)))
            | FStar_Pervasives_Native.None ->
                let uu____2381 =
                  let uu____2387 =
                    let uu____2389 =
                      FStar_Syntax_Print.lid_to_string
                        c11.FStar_Syntax_Syntax.effect_name in
                    let uu____2391 =
                      FStar_Syntax_Print.lid_to_string
                        c21.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2 "Effects %s and %s cannot be composed"
                      uu____2389 uu____2391 in
                  (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____2387) in
                FStar_Errors.raise_error uu____2381
                  env.FStar_TypeChecker_Env.range
let (lift_comps :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
          Prims.bool ->
            (FStar_Ident.lident * FStar_Syntax_Syntax.comp *
              FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun c1 ->
      fun c2 ->
        fun b ->
          fun for_bind ->
            let uu____2453 = lift_comps_sep_guards env c1 c2 b for_bind in
            match uu____2453 with
            | (l, c11, c21, g1, g2) ->
                let uu____2477 = FStar_TypeChecker_Env.conj_guard g1 g2 in
                (l, c11, c21, uu____2477)
let (is_pure_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun l ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l in
      FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid
let (is_pure_or_ghost_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun l ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l in
      (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid) ||
        (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid)
let (lax_mk_tot_or_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname ->
    fun u_result ->
      fun result ->
        fun flags ->
          let uu____2533 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid in
          if uu____2533
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____2545 =
      let uu____2546 = FStar_Syntax_Subst.compress t in
      uu____2546.FStar_Syntax_Syntax.n in
    match uu____2545 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2550 -> true
    | uu____2566 -> false
let (label :
  Prims.string ->
    FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun reason ->
    fun r ->
      fun f ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_meta
             (f, (FStar_Syntax_Syntax.Meta_labeled (reason, r, false))))
          f.FStar_Syntax_Syntax.pos
let (label_opt :
  FStar_TypeChecker_Env.env ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env ->
    fun reason ->
      fun r ->
        fun f ->
          match reason with
          | FStar_Pervasives_Native.None -> f
          | FStar_Pervasives_Native.Some reason1 ->
              let uu____2636 =
                let uu____2638 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____2638 in
              if uu____2636
              then f
              else (let uu____2645 = reason1 () in label uu____2645 r f)
let (label_guard :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun r ->
    fun reason ->
      fun g ->
        match g.FStar_TypeChecker_Common.guard_f with
        | FStar_TypeChecker_Common.Trivial -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___351_2666 = g in
            let uu____2667 =
              let uu____2668 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____2668 in
            {
              FStar_TypeChecker_Common.guard_f = uu____2667;
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___351_2666.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___351_2666.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___351_2666.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___351_2666.FStar_TypeChecker_Common.implicits)
            }
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun bvs ->
      fun c ->
        let uu____2689 = FStar_Syntax_Util.is_ml_comp c in
        if uu____2689
        then c
        else
          (let uu____2694 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____2694
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close =
                  let uu____2736 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator in
                  FStar_All.pipe_right uu____2736 FStar_Util.must in
                FStar_List.fold_right
                  (fun x ->
                     fun wp ->
                       let bs =
                         let uu____2765 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____2765] in
                       let us =
                         let uu____2787 =
                           let uu____2790 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____2790] in
                         u_res :: uu____2787 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu____2796 =
                         FStar_TypeChecker_Env.inst_effect_fun_with us env md
                           close in
                       let uu____2797 =
                         let uu____2798 = FStar_Syntax_Syntax.as_arg res_t in
                         let uu____2807 =
                           let uu____2818 =
                             FStar_Syntax_Syntax.as_arg
                               x.FStar_Syntax_Syntax.sort in
                           let uu____2827 =
                             let uu____2838 = FStar_Syntax_Syntax.as_arg wp1 in
                             [uu____2838] in
                           uu____2818 :: uu____2827 in
                         uu____2798 :: uu____2807 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____2796 uu____2797
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____2880 = destruct_wp_comp c1 in
              match uu____2880 with
              | (u_res_t, res_t, wp) ->
                  let md =
                    FStar_TypeChecker_Env.get_effect_decl env
                      c1.FStar_Syntax_Syntax.effect_name in
                  let wp1 = close_wp u_res_t md res_t bvs wp in
                  mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1
                    c1.FStar_Syntax_Syntax.flags))
let (close_wp_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env ->
    fun bvs ->
      fun lc ->
        let bs =
          FStar_All.pipe_right bvs
            (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
        FStar_All.pipe_right lc
          (FStar_TypeChecker_Common.apply_lcomp (close_wp_comp env bvs)
             (fun g ->
                let uu____2920 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs) in
                FStar_All.pipe_right uu____2920
                  (close_guard_implicits env false bs)))
let (close_layered_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.term Prims.list ->
        FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env ->
    fun bvs ->
      fun tms ->
        fun lc ->
          let bs =
            FStar_All.pipe_right bvs
              (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
          let substs =
            FStar_List.map2
              (fun bv -> fun tm -> FStar_Syntax_Syntax.NT (bv, tm)) bvs tms in
          FStar_All.pipe_right lc
            (FStar_TypeChecker_Common.apply_lcomp
               (FStar_Syntax_Subst.subst_comp substs)
               (fun g ->
                  let uu____2970 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs) in
                  FStar_All.pipe_right uu____2970
                    (close_guard_implicits env false bs)))
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_2983 ->
            match uu___0_2983 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> true
            | uu____2986 -> false))
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env ->
    fun eopt ->
      fun lc ->
        let lc_is_unit_or_effectful =
          let uu____3011 =
            let uu____3014 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp in
            FStar_All.pipe_right uu____3014 FStar_Pervasives_Native.snd in
          FStar_All.pipe_right uu____3011
            (fun c ->
               (let uu____3038 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c in
                Prims.op_Negation uu____3038) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____3042 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c in
                     Prims.op_Negation uu____3042))) in
        match eopt with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____3053 = FStar_Syntax_Util.head_and_args' e in
                match uu____3053 with
                | (head, uu____3070) ->
                    let uu____3091 =
                      let uu____3092 = FStar_Syntax_Util.un_uinst head in
                      uu____3092.FStar_Syntax_Syntax.n in
                    (match uu____3091 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____3097 =
                           let uu____3099 = FStar_Syntax_Syntax.lid_of_fv fv in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____3099 in
                         Prims.op_Negation uu____3097
                     | uu____3100 -> true)))
              &&
              (let uu____3103 = should_not_inline_lc lc in
               Prims.op_Negation uu____3103)
let (return_value :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun eff_lid ->
      fun u_t_opt ->
        fun t ->
          fun v ->
            let u =
              match u_t_opt with
              | FStar_Pervasives_Native.None ->
                  env.FStar_TypeChecker_Env.universe_of env t
              | FStar_Pervasives_Native.Some u -> u in
            let uu____3149 =
              FStar_TypeChecker_Env.get_effect_decl env eff_lid in
            mk_return env uu____3149 u t v v.FStar_Syntax_Syntax.pos
let (mk_indexed_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.tscheme ->
            FStar_Syntax_Syntax.comp_typ ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Syntax_Syntax.comp_typ ->
                  FStar_Syntax_Syntax.cflag Prims.list ->
                    FStar_Range.range ->
                      (FStar_Syntax_Syntax.comp *
                        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun m ->
      fun n ->
        fun p ->
          fun bind_t ->
            fun ct1 ->
              fun b ->
                fun ct2 ->
                  fun flags ->
                    fun r1 ->
                      let bind_name =
                        let uu____3219 =
                          let uu____3221 =
                            FStar_All.pipe_right m FStar_Ident.ident_of_lid in
                          FStar_All.pipe_right uu____3221
                            FStar_Ident.string_of_id in
                        let uu____3223 =
                          let uu____3225 =
                            FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                          FStar_All.pipe_right uu____3225
                            FStar_Ident.string_of_id in
                        let uu____3227 =
                          let uu____3229 =
                            FStar_All.pipe_right p FStar_Ident.ident_of_lid in
                          FStar_All.pipe_right uu____3229
                            FStar_Ident.string_of_id in
                        FStar_Util.format3 "(%s, %s) |> %s" uu____3219
                          uu____3223 uu____3227 in
                      (let uu____3233 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LayeredEffects") in
                       if uu____3233
                       then
                         let uu____3238 =
                           let uu____3240 = FStar_Syntax_Syntax.mk_Comp ct1 in
                           FStar_Syntax_Print.comp_to_string uu____3240 in
                         let uu____3241 =
                           let uu____3243 = FStar_Syntax_Syntax.mk_Comp ct2 in
                           FStar_Syntax_Print.comp_to_string uu____3243 in
                         FStar_Util.print2 "Binding c1:%s and c2:%s {\n"
                           uu____3238 uu____3241
                       else ());
                      (let uu____3248 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "ResolveImplicitsHook") in
                       if uu____3248
                       then
                         let uu____3253 =
                           let uu____3255 =
                             FStar_TypeChecker_Env.get_range env in
                           FStar_Range.string_of_range uu____3255 in
                         let uu____3256 =
                           FStar_Syntax_Print.tscheme_to_string bind_t in
                         FStar_Util.print2
                           "///////////////////////////////Bind at %s/////////////////////\nwith bind_t = %s\n"
                           uu____3253 uu____3256
                       else ());
                      (let uu____3261 =
                         let uu____3268 =
                           FStar_TypeChecker_Env.get_effect_decl env m in
                         let uu____3269 =
                           FStar_TypeChecker_Env.get_effect_decl env n in
                         let uu____3270 =
                           FStar_TypeChecker_Env.get_effect_decl env p in
                         (uu____3268, uu____3269, uu____3270) in
                       match uu____3261 with
                       | (m_ed, n_ed, p_ed) ->
                           let uu____3278 =
                             let uu____3291 =
                               FStar_List.hd
                                 ct1.FStar_Syntax_Syntax.comp_univs in
                             let uu____3292 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 ct1.FStar_Syntax_Syntax.effect_args in
                             (uu____3291,
                               (ct1.FStar_Syntax_Syntax.result_typ),
                               uu____3292) in
                           (match uu____3278 with
                            | (u1, t1, is1) ->
                                let uu____3336 =
                                  let uu____3349 =
                                    FStar_List.hd
                                      ct2.FStar_Syntax_Syntax.comp_univs in
                                  let uu____3350 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst
                                      ct2.FStar_Syntax_Syntax.effect_args in
                                  (uu____3349,
                                    (ct2.FStar_Syntax_Syntax.result_typ),
                                    uu____3350) in
                                (match uu____3336 with
                                 | (u2, t2, is2) ->
                                     let uu____3394 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         bind_t [u1; u2] in
                                     (match uu____3394 with
                                      | (uu____3403, bind_t1) ->
                                          let bind_t_shape_error s =
                                            let uu____3418 =
                                              let uu____3420 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t1 in
                                              FStar_Util.format3
                                                "bind %s (%s) does not have proper shape (reason:%s)"
                                                uu____3420 bind_name s in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu____3418) in
                                          let uu____3424 =
                                            let uu____3469 =
                                              let uu____3470 =
                                                FStar_Syntax_Subst.compress
                                                  bind_t1 in
                                              uu____3470.FStar_Syntax_Syntax.n in
                                            match uu____3469 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs, c) when
                                                (FStar_List.length bs) >=
                                                  (Prims.of_int (4))
                                                ->
                                                let uu____3546 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs c in
                                                (match uu____3546 with
                                                 | (a_b::b_b::bs1, c1) ->
                                                     let uu____3631 =
                                                       let uu____3658 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2)))
                                                           bs1 in
                                                       FStar_All.pipe_right
                                                         uu____3658
                                                         (fun uu____3743 ->
                                                            match uu____3743
                                                            with
                                                            | (l1, l2) ->
                                                                let uu____3824
                                                                  =
                                                                  FStar_List.hd
                                                                    l2 in
                                                                let uu____3837
                                                                  =
                                                                  let uu____3844
                                                                    =
                                                                    FStar_List.tl
                                                                    l2 in
                                                                  FStar_List.hd
                                                                    uu____3844 in
                                                                (l1,
                                                                  uu____3824,
                                                                  uu____3837)) in
                                                     (match uu____3631 with
                                                      | (rest_bs, f_b, g_b)
                                                          ->
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b, c1)))
                                            | uu____4004 ->
                                                let uu____4005 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders" in
                                                FStar_Errors.raise_error
                                                  uu____4005 r1 in
                                          (match uu____3424 with
                                           | (a_b, b_b, rest_bs, f_b, g_b,
                                              bind_c) ->
                                               let uu____4130 =
                                                 let uu____4137 =
                                                   let uu____4138 =
                                                     let uu____4139 =
                                                       let uu____4146 =
                                                         FStar_All.pipe_right
                                                           a_b
                                                           FStar_Pervasives_Native.fst in
                                                       (uu____4146, t1) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____4139 in
                                                   let uu____4157 =
                                                     let uu____4160 =
                                                       let uu____4161 =
                                                         let uu____4168 =
                                                           FStar_All.pipe_right
                                                             b_b
                                                             FStar_Pervasives_Native.fst in
                                                         (uu____4168, t2) in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____4161 in
                                                     [uu____4160] in
                                                   uu____4138 :: uu____4157 in
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs uu____4137
                                                   (fun b1 ->
                                                      let uu____4183 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1 in
                                                      let uu____4185 =
                                                        FStar_Range.string_of_range
                                                          r1 in
                                                      FStar_Util.format3
                                                        "implicit var for binder %s of %s at %s"
                                                        uu____4183 bind_name
                                                        uu____4185) r1 in
                                               (match uu____4130 with
                                                | (rest_bs_uvars, g_uvars) ->
                                                    ((let uu____4199 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "ResolveImplicitsHook") in
                                                      if uu____4199
                                                      then
                                                        FStar_All.pipe_right
                                                          rest_bs_uvars
                                                          (FStar_List.iter
                                                             (fun t ->
                                                                let uu____4213
                                                                  =
                                                                  let uu____4214
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    t in
                                                                  uu____4214.FStar_Syntax_Syntax.n in
                                                                match uu____4213
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (u,
                                                                    uu____4218)
                                                                    ->
                                                                    let uu____4235
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t in
                                                                    let uu____4237
                                                                    =
                                                                    match 
                                                                    u.FStar_Syntax_Syntax.ctx_uvar_meta
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Ctx_uvar_meta_attr
                                                                    a) ->
                                                                    FStar_Syntax_Print.term_to_string
                                                                    a
                                                                    | 
                                                                    uu____4243
                                                                    ->
                                                                    "<no attr>" in
                                                                    FStar_Util.print2
                                                                    "Generated uvar %s with attribute %s\n"
                                                                    uu____4235
                                                                    uu____4237))
                                                      else ());
                                                     (let subst =
                                                        FStar_List.map2
                                                          (fun b1 ->
                                                             fun t ->
                                                               let uu____4274
                                                                 =
                                                                 let uu____4281
                                                                   =
                                                                   FStar_All.pipe_right
                                                                    b1
                                                                    FStar_Pervasives_Native.fst in
                                                                 (uu____4281,
                                                                   t) in
                                                               FStar_Syntax_Syntax.NT
                                                                 uu____4274)
                                                          (a_b :: b_b ::
                                                          rest_bs) (t1 :: t2
                                                          :: rest_bs_uvars) in
                                                      let f_guard =
                                                        let f_sort_is =
                                                          let uu____4310 =
                                                            let uu____4313 =
                                                              let uu____4314
                                                                =
                                                                let uu____4315
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    f_b
                                                                    FStar_Pervasives_Native.fst in
                                                                uu____4315.FStar_Syntax_Syntax.sort in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4314 in
                                                            let uu____4324 =
                                                              FStar_Syntax_Util.is_layered
                                                                m_ed in
                                                            effect_args_from_repr
                                                              uu____4313
                                                              uu____4324 r1 in
                                                          FStar_All.pipe_right
                                                            uu____4310
                                                            (FStar_List.map
                                                               (FStar_Syntax_Subst.subst
                                                                  subst)) in
                                                        FStar_List.fold_left2
                                                          (fun g ->
                                                             fun i1 ->
                                                               fun f_i1 ->
                                                                 (let uu____4349
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "ResolveImplicitsHook") in
                                                                  if
                                                                    uu____4349
                                                                  then
                                                                    let uu____4354
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    i1 in
                                                                    let uu____4356
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    f_i1 in
                                                                    FStar_Util.print2
                                                                    "Generating constraint %s = %s\n"
                                                                    uu____4354
                                                                    uu____4356
                                                                  else ());
                                                                 (let uu____4361
                                                                    =
                                                                    FStar_TypeChecker_Rel.layered_effect_teq
                                                                    env i1
                                                                    f_i1
                                                                    (FStar_Pervasives_Native.Some
                                                                    bind_name) in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____4361))
                                                          FStar_TypeChecker_Env.trivial_guard
                                                          is1 f_sort_is in
                                                      let g_guard =
                                                        let x_a =
                                                          match b with
                                                          | FStar_Pervasives_Native.None
                                                              ->
                                                              FStar_Syntax_Syntax.null_binder
                                                                ct1.FStar_Syntax_Syntax.result_typ
                                                          | FStar_Pervasives_Native.Some
                                                              x ->
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x in
                                                        let g_sort_is =
                                                          let uu____4381 =
                                                            let uu____4382 =
                                                              let uu____4385
                                                                =
                                                                let uu____4386
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    g_b
                                                                    FStar_Pervasives_Native.fst in
                                                                uu____4386.FStar_Syntax_Syntax.sort in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4385 in
                                                            uu____4382.FStar_Syntax_Syntax.n in
                                                          match uu____4381
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_arrow
                                                              (bs, c) ->
                                                              let uu____4419
                                                                =
                                                                FStar_Syntax_Subst.open_comp
                                                                  bs c in
                                                              (match uu____4419
                                                               with
                                                               | (bs1, c1) ->
                                                                   let bs_subst
                                                                    =
                                                                    let uu____4429
                                                                    =
                                                                    let uu____4436
                                                                    =
                                                                    let uu____4437
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1 in
                                                                    FStar_All.pipe_right
                                                                    uu____4437
                                                                    FStar_Pervasives_Native.fst in
                                                                    let uu____4458
                                                                    =
                                                                    let uu____4461
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst in
                                                                    FStar_All.pipe_right
                                                                    uu____4461
                                                                    FStar_Syntax_Syntax.bv_to_name in
                                                                    (uu____4436,
                                                                    uu____4458) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4429 in
                                                                   let c2 =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1 in
                                                                   let uu____4475
                                                                    =
                                                                    let uu____4478
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2) in
                                                                    let uu____4479
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed in
                                                                    effect_args_from_repr
                                                                    uu____4478
                                                                    uu____4479
                                                                    r1 in
                                                                   FStar_All.pipe_right
                                                                    uu____4475
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst)))
                                                          | uu____4485 ->
                                                              failwith
                                                                "impossible: mk_indexed_bind" in
                                                        let env_g =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env [x_a] in
                                                        let uu____4502 =
                                                          FStar_List.fold_left2
                                                            (fun g ->
                                                               fun i1 ->
                                                                 fun g_i1 ->
                                                                   (let uu____4520
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "ResolveImplicitsHook") in
                                                                    if
                                                                    uu____4520
                                                                    then
                                                                    let uu____4525
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    i1 in
                                                                    let uu____4527
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    g_i1 in
                                                                    FStar_Util.print2
                                                                    "Generating constraint %s = %s\n"
                                                                    uu____4525
                                                                    uu____4527
                                                                    else ());
                                                                   (let uu____4532
                                                                    =
                                                                    FStar_TypeChecker_Rel.layered_effect_teq
                                                                    env_g i1
                                                                    g_i1
                                                                    (FStar_Pervasives_Native.Some
                                                                    bind_name) in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____4532))
                                                            FStar_TypeChecker_Env.trivial_guard
                                                            is2 g_sort_is in
                                                        FStar_All.pipe_right
                                                          uu____4502
                                                          (FStar_TypeChecker_Env.close_guard
                                                             env [x_a]) in
                                                      let bind_ct =
                                                        let uu____4547 =
                                                          FStar_All.pipe_right
                                                            bind_c
                                                            (FStar_Syntax_Subst.subst_comp
                                                               subst) in
                                                        FStar_All.pipe_right
                                                          uu____4547
                                                          FStar_Syntax_Util.comp_to_comp_typ in
                                                      let fml =
                                                        let uu____4549 =
                                                          let uu____4554 =
                                                            FStar_List.hd
                                                              bind_ct.FStar_Syntax_Syntax.comp_univs in
                                                          let uu____4555 =
                                                            let uu____4556 =
                                                              FStar_List.hd
                                                                bind_ct.FStar_Syntax_Syntax.effect_args in
                                                            FStar_Pervasives_Native.fst
                                                              uu____4556 in
                                                          (uu____4554,
                                                            uu____4555) in
                                                        match uu____4549 with
                                                        | (u, wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              bind_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange in
                                                      let is =
                                                        let uu____4582 =
                                                          FStar_Syntax_Subst.compress
                                                            bind_ct.FStar_Syntax_Syntax.result_typ in
                                                        let uu____4583 =
                                                          FStar_Syntax_Util.is_layered
                                                            p_ed in
                                                        effect_args_from_repr
                                                          uu____4582
                                                          uu____4583 r1 in
                                                      let c =
                                                        let uu____4586 =
                                                          let uu____4587 =
                                                            FStar_List.map
                                                              FStar_Syntax_Syntax.as_arg
                                                              is in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              =
                                                              (ct2.FStar_Syntax_Syntax.comp_univs);
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              (p_ed.FStar_Syntax_Syntax.mname);
                                                            FStar_Syntax_Syntax.result_typ
                                                              = t2;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____4587;
                                                            FStar_Syntax_Syntax.flags
                                                              = flags
                                                          } in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____4586 in
                                                      (let uu____4607 =
                                                         FStar_All.pipe_left
                                                           (FStar_TypeChecker_Env.debug
                                                              env)
                                                           (FStar_Options.Other
                                                              "LayeredEffects") in
                                                       if uu____4607
                                                       then
                                                         let uu____4612 =
                                                           FStar_Syntax_Print.comp_to_string
                                                             c in
                                                         FStar_Util.print1
                                                           "} c after bind: %s\n"
                                                           uu____4612
                                                       else ());
                                                      (let guard =
                                                         let uu____4618 =
                                                           let uu____4621 =
                                                             let uu____4624 =
                                                               let uu____4627
                                                                 =
                                                                 let uu____4630
                                                                   =
                                                                   FStar_TypeChecker_Env.guard_of_guard_formula
                                                                    (FStar_TypeChecker_Common.NonTrivial
                                                                    fml) in
                                                                 [uu____4630] in
                                                               g_guard ::
                                                                 uu____4627 in
                                                             f_guard ::
                                                               uu____4624 in
                                                           g_uvars ::
                                                             uu____4621 in
                                                         FStar_TypeChecker_Env.conj_guards
                                                           uu____4618 in
                                                       (let uu____4632 =
                                                          FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "ResolveImplicitsHook") in
                                                        if uu____4632
                                                        then
                                                          let uu____4637 =
                                                            let uu____4639 =
                                                              FStar_TypeChecker_Env.get_range
                                                                env in
                                                            FStar_Range.string_of_range
                                                              uu____4639 in
                                                          let uu____4640 =
                                                            FStar_TypeChecker_Rel.guard_to_string
                                                              env guard in
                                                          FStar_Util.print2
                                                            "///////////////////////////////EndBind at %s/////////////////////\nguard = %s\n"
                                                            uu____4637
                                                            uu____4640
                                                        else ());
                                                       (c, guard))))))))))
let (mk_wp_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.comp_typ ->
        FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
          FStar_Syntax_Syntax.comp_typ ->
            FStar_Syntax_Syntax.cflag Prims.list ->
              FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun m ->
      fun ct1 ->
        fun b ->
          fun ct2 ->
            fun flags ->
              fun r1 ->
                let uu____4689 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m in
                  let uu____4715 = FStar_TypeChecker_Env.wp_signature env m in
                  match uu____4715 with
                  | (a, kwp) ->
                      let uu____4746 = destruct_wp_comp ct1 in
                      let uu____4753 = destruct_wp_comp ct2 in
                      ((md, a, kwp), uu____4746, uu____4753) in
                match uu____4689 with
                | ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None ->
                          let uu____4806 = FStar_Syntax_Syntax.null_binder t1 in
                          [uu____4806]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____4826 = FStar_Syntax_Syntax.mk_binder x in
                          [uu____4826] in
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
                           (FStar_Const.Const_range r1)) r1 in
                    let wp_args =
                      let uu____4873 = FStar_Syntax_Syntax.as_arg r11 in
                      let uu____4882 =
                        let uu____4893 = FStar_Syntax_Syntax.as_arg t1 in
                        let uu____4902 =
                          let uu____4913 = FStar_Syntax_Syntax.as_arg t2 in
                          let uu____4922 =
                            let uu____4933 = FStar_Syntax_Syntax.as_arg wp1 in
                            let uu____4942 =
                              let uu____4953 =
                                let uu____4962 = mk_lam wp2 in
                                FStar_Syntax_Syntax.as_arg uu____4962 in
                              [uu____4953] in
                            uu____4933 :: uu____4942 in
                          uu____4913 :: uu____4922 in
                        uu____4893 :: uu____4902 in
                      uu____4873 :: uu____4882 in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator in
                    let wp =
                      let uu____5013 =
                        FStar_TypeChecker_Env.inst_effect_fun_with
                          [u_t1; u_t2] env md bind_wp in
                      FStar_Syntax_Syntax.mk_Tm_app uu____5013 wp_args
                        t2.FStar_Syntax_Syntax.pos in
                    mk_comp md u_t2 t2 wp flags
let (mk_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.comp ->
          FStar_Syntax_Syntax.cflag Prims.list ->
            FStar_Range.range ->
              (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun c1 ->
      fun b ->
        fun c2 ->
          fun flags ->
            fun r1 ->
              let uu____5061 =
                let uu____5066 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1 in
                let uu____5067 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2 in
                (uu____5066, uu____5067) in
              match uu____5061 with
              | (ct1, ct2) ->
                  let uu____5074 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name in
                  (match uu____5074 with
                   | FStar_Pervasives_Native.Some (p, f_bind) ->
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None ->
                       let uu____5125 = lift_comps env c1 c2 b true in
                       (match uu____5125 with
                        | (m, c11, c21, g_lift) ->
                            let uu____5143 =
                              let uu____5148 =
                                FStar_Syntax_Util.comp_to_comp_typ c11 in
                              let uu____5149 =
                                FStar_Syntax_Util.comp_to_comp_typ c21 in
                              (uu____5148, uu____5149) in
                            (match uu____5143 with
                             | (ct11, ct21) ->
                                 let uu____5156 =
                                   let uu____5161 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m in
                                   if uu____5161
                                   then
                                     let bind_t =
                                       let uu____5169 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env) in
                                       FStar_All.pipe_right uu____5169
                                         FStar_Syntax_Util.get_bind_vc_combinator in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu____5172 =
                                        mk_wp_bind env m ct11 b ct21 flags r1 in
                                      (uu____5172,
                                        FStar_TypeChecker_Env.trivial_guard)) in
                                 (match uu____5156 with
                                  | (c, g_bind) ->
                                      let uu____5179 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind in
                                      (c, uu____5179)))))
let (bind_pure_wp_with :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.cflag Prims.list ->
          (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun wp1 ->
      fun c ->
        fun flags ->
          let r = FStar_TypeChecker_Env.get_range env in
          let pure_c =
            let uu____5215 =
              let uu____5216 =
                let uu____5227 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg in
                [uu____5227] in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____5216;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____5215 in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags ->
    let uu____5272 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_5278 ->
              match uu___1_5278 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> true
              | uu____5281 -> false)) in
    if uu____5272
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_5293 ->
              match uu___2_5293 with
              | FStar_Syntax_Syntax.TOTAL ->
                  [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | FStar_Syntax_Syntax.RETURN ->
                  [FStar_Syntax_Syntax.PARTIAL_RETURN;
                  FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | f -> [f]))
let (weaken_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun c ->
      fun formula ->
        let uu____5321 = FStar_Syntax_Util.is_ml_comp c in
        if uu____5321
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
           let pure_assume_wp =
             let uu____5332 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None in
             FStar_Syntax_Syntax.fv_to_tm uu____5332 in
           let pure_assume_wp1 =
             let uu____5335 =
               let uu____5336 =
                 FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula in
               [uu____5336] in
             let uu____5369 = FStar_TypeChecker_Env.get_range env in
             FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____5335
               uu____5369 in
           let uu____5370 = weaken_flags ct.FStar_Syntax_Syntax.flags in
           bind_pure_wp_with env pure_assume_wp1 c uu____5370)
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env ->
    fun lc ->
      fun f ->
        let weaken uu____5398 =
          let uu____5399 = FStar_TypeChecker_Common.lcomp_comp lc in
          match uu____5399 with
          | (c, g_c) ->
              let uu____5410 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
              if uu____5410
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5424 = weaken_comp env c f1 in
                     (match uu____5424 with
                      | (c1, g_w) ->
                          let uu____5435 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w in
                          (c1, uu____5435))) in
        let uu____5436 = weaken_flags lc.FStar_TypeChecker_Common.cflags in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5436 weaken
let (strengthen_comp :
  FStar_TypeChecker_Env.env ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.formula ->
          FStar_Syntax_Syntax.cflag Prims.list ->
            (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun reason ->
      fun c ->
        fun f ->
          fun flags ->
            if env.FStar_TypeChecker_Env.lax
            then (c, FStar_TypeChecker_Env.trivial_guard)
            else
              (let r = FStar_TypeChecker_Env.get_range env in
               let pure_assert_wp =
                 let uu____5493 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None in
                 FStar_Syntax_Syntax.fv_to_tm uu____5493 in
               let pure_assert_wp1 =
                 let uu____5496 =
                   let uu____5497 =
                     let uu____5506 = label_opt env reason r f in
                     FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                       uu____5506 in
                   [uu____5497] in
                 FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____5496 r in
               bind_pure_wp_with env pure_assert_wp1 c flags)
let (strengthen_precondition :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.lcomp ->
          FStar_TypeChecker_Common.guard_t ->
            (FStar_TypeChecker_Common.lcomp *
              FStar_TypeChecker_Common.guard_t))
  =
  fun reason ->
    fun env ->
      fun e_for_debugging_only ->
        fun lc ->
          fun g0 ->
            let uu____5576 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0 in
            if uu____5576
            then (lc, g0)
            else
              (let flags =
                 let uu____5588 =
                   let uu____5596 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc in
                   if uu____5596
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, []) in
                 match uu____5588 with
                 | (maybe_trivial_post, flags) ->
                     let uu____5626 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_5634 ->
                               match uu___3_5634 with
                               | FStar_Syntax_Syntax.RETURN ->
                                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                               | FStar_Syntax_Syntax.PARTIAL_RETURN ->
                                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                               | FStar_Syntax_Syntax.SOMETRIVIAL when
                                   Prims.op_Negation maybe_trivial_post ->
                                   [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
                               | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION
                                   when Prims.op_Negation maybe_trivial_post
                                   ->
                                   [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
                               | FStar_Syntax_Syntax.SHOULD_NOT_INLINE ->
                                   [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                               | uu____5637 -> [])) in
                     FStar_List.append flags uu____5626 in
               let strengthen uu____5647 =
                 let uu____5648 = FStar_TypeChecker_Common.lcomp_comp lc in
                 match uu____5648 with
                 | (c, g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                        let uu____5667 = FStar_TypeChecker_Env.guard_form g01 in
                        match uu____5667 with
                        | FStar_TypeChecker_Common.Trivial -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____5674 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____5674
                              then
                                let uu____5678 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only in
                                let uu____5680 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____5678 uu____5680
                              else ());
                             (let uu____5685 =
                                strengthen_comp env reason c f flags in
                              match uu____5685 with
                              | (c1, g_s) ->
                                  let uu____5696 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s in
                                  (c1, uu____5696)))) in
               let uu____5697 =
                 let uu____5698 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name in
                 FStar_TypeChecker_Common.mk_lcomp uu____5698
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen in
               (uu____5697,
                 (let uu___675_5700 = g0 in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred_to_tac =
                      (uu___675_5700.FStar_TypeChecker_Common.deferred_to_tac);
                    FStar_TypeChecker_Common.deferred =
                      (uu___675_5700.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___675_5700.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___675_5700.FStar_TypeChecker_Common.implicits)
                  })))
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_5709 ->
            match uu___4_5709 with
            | FStar_Syntax_Syntax.SOMETRIVIAL -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION -> true
            | uu____5713 -> false) lc.FStar_TypeChecker_Common.cflags)
let (maybe_add_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env ->
    fun uopt ->
      fun lc ->
        fun e ->
          let uu____5742 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax in
          if uu____5742
          then e
          else
            (let uu____5749 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____5752 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid in
                  FStar_Option.isSome uu____5752) in
             if uu____5749
             then
               let u =
                 match uopt with
                 | FStar_Pervasives_Native.Some u -> u
                 | FStar_Pervasives_Native.None ->
                     env.FStar_TypeChecker_Env.universe_of env
                       lc.FStar_TypeChecker_Common.res_typ in
               FStar_Syntax_Util.mk_with_type u
                 lc.FStar_TypeChecker_Common.res_typ e
             else e)
let (maybe_capture_unit_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun t ->
      fun x ->
        fun c ->
          let t1 =
            FStar_TypeChecker_Normalize.normalize_refinement
              FStar_TypeChecker_Normalize.whnf_steps env t in
          match t1.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (b, phi) ->
              let is_unit =
                match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.unit_lid
                | uu____5822 -> false in
              if is_unit
              then
                let uu____5829 =
                  let uu____5831 =
                    let uu____5832 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name in
                    FStar_All.pipe_right uu____5832
                      (FStar_TypeChecker_Env.norm_eff_name env) in
                  FStar_All.pipe_right uu____5831
                    (FStar_TypeChecker_Env.is_layered_effect env) in
                (if uu____5829
                 then
                   let uu____5841 = FStar_Syntax_Subst.open_term_bv b phi in
                   match uu____5841 with
                   | (b1, phi1) ->
                       let phi2 =
                         FStar_Syntax_Subst.subst
                           [FStar_Syntax_Syntax.NT
                              (b1, FStar_Syntax_Syntax.unit_const)] phi1 in
                       weaken_comp env c phi2
                 else
                   (let uu____5857 = close_wp_comp env [x] c in
                    (uu____5857, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____5860 -> (c, FStar_TypeChecker_Env.trivial_guard)
let (bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Common.lcomp ->
          lcomp_with_binder -> FStar_TypeChecker_Common.lcomp)
  =
  fun r1 ->
    fun env ->
      fun e1opt ->
        fun lc1 ->
          fun uu____5888 ->
            match uu____5888 with
            | (b, lc2) ->
                let debug f =
                  let uu____5908 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____5908 then f () else () in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                let bind_flags =
                  let uu____5921 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21) in
                  if uu____5921
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____5931 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11 in
                       if uu____5931
                       then
                         let uu____5936 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21 in
                         (if uu____5936
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5943 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21 in
                             if uu____5943
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5952 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21) in
                          if uu____5952
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else []) in
                     let uu____5959 = lcomp_has_trivial_postcondition lc21 in
                     if uu____5959
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags) in
                let bind_it uu____5975 =
                  let uu____5976 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ()) in
                  if uu____5976
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ in
                    let uu____5984 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ [] in
                    (uu____5984, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____5987 =
                       FStar_TypeChecker_Common.lcomp_comp lc11 in
                     match uu____5987 with
                     | (c1, g_c1) ->
                         let uu____5998 =
                           FStar_TypeChecker_Common.lcomp_comp lc21 in
                         (match uu____5998 with
                          | (c2, g_c2) ->
                              let trivial_guard =
                                let uu____6010 =
                                  match b with
                                  | FStar_Pervasives_Native.Some x ->
                                      let b1 =
                                        FStar_Syntax_Syntax.mk_binder x in
                                      let uu____6013 =
                                        FStar_Syntax_Syntax.is_null_binder b1 in
                                      if uu____6013
                                      then g_c2
                                      else
                                        FStar_TypeChecker_Env.close_guard env
                                          [b1] g_c2
                                  | FStar_Pervasives_Native.None -> g_c2 in
                                FStar_TypeChecker_Env.conj_guard g_c1
                                  uu____6010 in
                              (debug
                                 (fun uu____6039 ->
                                    let uu____6040 =
                                      FStar_Syntax_Print.comp_to_string c1 in
                                    let uu____6042 =
                                      match b with
                                      | FStar_Pervasives_Native.None ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x in
                                    let uu____6047 =
                                      FStar_Syntax_Print.comp_to_string c2 in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____6040 uu____6042 uu____6047);
                               (let aux uu____6065 =
                                  let uu____6066 =
                                    FStar_Syntax_Util.is_trivial_wp c1 in
                                  if uu____6066
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____6097
                                        ->
                                        let uu____6098 =
                                          FStar_Syntax_Util.is_ml_comp c2 in
                                        (if uu____6098
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____6130 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2) in
                                     if uu____6130
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML") in
                                let try_simplify uu____6177 =
                                  let aux_with_trivial_guard uu____6207 =
                                    let uu____6208 = aux () in
                                    match uu____6208 with
                                    | FStar_Util.Inl (c, reason) ->
                                        FStar_Util.Inl
                                          (c, trivial_guard, reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason in
                                  let uu____6266 =
                                    let uu____6268 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid in
                                    FStar_Option.isNone uu____6268 in
                                  if uu____6266
                                  then
                                    let uu____6284 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2) in
                                    (if uu____6284
                                     then
                                       FStar_Util.Inl
                                         (c2, trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____6311 =
                                          FStar_TypeChecker_Env.get_range env in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____6311))
                                  else
                                    (let uu____6328 =
                                       FStar_Syntax_Util.is_total_comp c1 in
                                     if uu____6328
                                     then
                                       let close_with_type_of_x x c =
                                         let x1 =
                                           let uu___778_6359 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___778_6359.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___778_6359.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         maybe_capture_unit_refinement env
                                           x1.FStar_Syntax_Syntax.sort x1 c in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some e,
                                          FStar_Pervasives_Native.Some x) ->
                                           let uu____6390 =
                                             let uu____6395 =
                                               FStar_All.pipe_right c2
                                                 (FStar_Syntax_Subst.subst_comp
                                                    [FStar_Syntax_Syntax.NT
                                                       (x, e)]) in
                                             FStar_All.pipe_right uu____6395
                                               (close_with_type_of_x x) in
                                           (match uu____6390 with
                                            | (c21, g_close) ->
                                                let uu____6416 =
                                                  let uu____6424 =
                                                    let uu____6425 =
                                                      let uu____6428 =
                                                        let uu____6431 =
                                                          FStar_TypeChecker_Env.map_guard
                                                            g_c2
                                                            (FStar_Syntax_Subst.subst
                                                               [FStar_Syntax_Syntax.NT
                                                                  (x, e)]) in
                                                        [uu____6431; g_close] in
                                                      g_c1 :: uu____6428 in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6425 in
                                                  (c21, uu____6424, "c1 Tot") in
                                                FStar_Util.Inl uu____6416)
                                       | (uu____6444,
                                          FStar_Pervasives_Native.Some x) ->
                                           let uu____6456 =
                                             FStar_All.pipe_right c2
                                               (close_with_type_of_x x) in
                                           (match uu____6456 with
                                            | (c21, g_close) ->
                                                let uu____6479 =
                                                  let uu____6487 =
                                                    let uu____6488 =
                                                      let uu____6491 =
                                                        let uu____6494 =
                                                          let uu____6495 =
                                                            let uu____6496 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x in
                                                            [uu____6496] in
                                                          FStar_TypeChecker_Env.close_guard
                                                            env uu____6495
                                                            g_c2 in
                                                        [uu____6494; g_close] in
                                                      g_c1 :: uu____6491 in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6488 in
                                                  (c21, uu____6487,
                                                    "c1 Tot only close") in
                                                FStar_Util.Inl uu____6479)
                                       | (uu____6525, uu____6526) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____6541 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2) in
                                        if uu____6541
                                        then
                                          let uu____6556 =
                                            let uu____6564 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2) in
                                            (uu____6564, trivial_guard,
                                              "both GTot") in
                                          FStar_Util.Inl uu____6556
                                        else aux_with_trivial_guard ())) in
                                let uu____6577 = try_simplify () in
                                match uu____6577 with
                                | FStar_Util.Inl (c, g, reason) ->
                                    (debug
                                       (fun uu____6612 ->
                                          let uu____6613 =
                                            FStar_Syntax_Print.comp_to_string
                                              c in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____6613);
                                     (c, g))
                                | FStar_Util.Inr reason ->
                                    (debug
                                       (fun uu____6629 ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 g =
                                        let uu____6660 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1 in
                                        match uu____6660 with
                                        | (c, g_bind) ->
                                            let uu____6671 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g g_bind in
                                            (c, uu____6671) in
                                      let mk_seq c11 b1 c21 =
                                        let c12 =
                                          FStar_TypeChecker_Env.unfold_effect_abbrev
                                            env c11 in
                                        let c22 =
                                          FStar_TypeChecker_Env.unfold_effect_abbrev
                                            env c21 in
                                        let uu____6698 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name in
                                        match uu____6698 with
                                        | (m, uu____6710, lift2) ->
                                            let uu____6712 =
                                              lift_comp env c22 lift2 in
                                            (match uu____6712 with
                                             | (c23, g2) ->
                                                 let uu____6723 =
                                                   destruct_wp_comp c12 in
                                                 (match uu____6723 with
                                                  | (u1, t1, wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name in
                                                      let trivial =
                                                        let uu____6739 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator in
                                                        FStar_All.pipe_right
                                                          uu____6739
                                                          FStar_Util.must in
                                                      let vc1 =
                                                        let uu____6747 =
                                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                                            [u1] env
                                                            md_pure_or_ghost
                                                            trivial in
                                                        let uu____6748 =
                                                          let uu____6749 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              t1 in
                                                          let uu____6758 =
                                                            let uu____6769 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                wp1 in
                                                            [uu____6769] in
                                                          uu____6749 ::
                                                            uu____6758 in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____6747
                                                          uu____6748 r1 in
                                                      let uu____6802 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags in
                                                      (match uu____6802 with
                                                       | (c, g_s) ->
                                                           let uu____6817 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s] in
                                                           (c, uu____6817)))) in
                                      let uu____6818 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1 in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None ->
                                            let uu____6834 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t in
                                            (uu____6834, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t) in
                                      match uu____6818 with
                                      | (u_res_t1, res_t1) ->
                                          let uu____6850 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11) in
                                          if uu____6850
                                          then
                                            let e1 = FStar_Option.get e1opt in
                                            let x = FStar_Option.get b in
                                            let uu____6859 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1 in
                                            (if uu____6859
                                             then
                                               (debug
                                                  (fun uu____6873 ->
                                                     let uu____6874 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1 in
                                                     let uu____6876 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____6874 uu____6876);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2 in
                                                 let g =
                                                   let uu____6883 =
                                                     FStar_TypeChecker_Env.map_guard
                                                       g_c2
                                                       (FStar_Syntax_Subst.subst
                                                          [FStar_Syntax_Syntax.NT
                                                             (x, e1)]) in
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 uu____6883 in
                                                 mk_bind1 c1 b c21 g))
                                             else
                                               (let uu____6888 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____6891 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid in
                                                     FStar_Option.isSome
                                                       uu____6891) in
                                                if uu____6888
                                                then
                                                  let e1' =
                                                    let uu____6916 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        () in
                                                    if uu____6916
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1 in
                                                  (debug
                                                     (fun uu____6928 ->
                                                        let uu____6929 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1' in
                                                        let uu____6931 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____6929
                                                          uu____6931);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2 in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug
                                                     (fun uu____6946 ->
                                                        let uu____6947 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1 in
                                                        let uu____6949 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____6947
                                                          uu____6949);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2 in
                                                    let x_eq_e =
                                                      let uu____6956 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____6956 in
                                                    let uu____6957 =
                                                      let uu____6962 =
                                                        let uu____6963 =
                                                          let uu____6964 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x in
                                                          [uu____6964] in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____6963 in
                                                      weaken_comp uu____6962
                                                        c21 x_eq_e in
                                                    match uu____6957 with
                                                    | (c22, g_w) ->
                                                        let g =
                                                          let uu____6990 =
                                                            let uu____6991 =
                                                              let uu____6992
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x in
                                                              [uu____6992] in
                                                            let uu____7011 =
                                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                                g_c2 x_eq_e in
                                                            FStar_TypeChecker_Env.close_guard
                                                              env uu____6991
                                                              uu____7011 in
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g_c1 uu____6990 in
                                                        let uu____7012 =
                                                          mk_bind1 c1 b c22 g in
                                                        (match uu____7012
                                                         with
                                                         | (c, g_bind) ->
                                                             let uu____7023 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind in
                                                             (c, uu____7023))))))
                                          else mk_bind1 c1 b c2 trivial_guard)))))) in
                FStar_TypeChecker_Common.mk_lcomp joined_eff
                  lc21.FStar_TypeChecker_Common.res_typ bind_flags bind_it
let (weaken_guard :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1 ->
    fun g2 ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.NonTrivial f1,
         FStar_TypeChecker_Common.NonTrivial f2) ->
          let g = FStar_Syntax_Util.mk_imp f1 f2 in
          FStar_TypeChecker_Common.NonTrivial g
      | uu____7040 -> g2
let (maybe_assume_result_eq_pure_term_in_m :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env ->
    fun m_opt ->
      fun e ->
        fun lc ->
          let should_return1 =
            (((Prims.op_Negation env.FStar_TypeChecker_Env.lax) &&
                (FStar_TypeChecker_Env.lid_exists env
                   FStar_Parser_Const.effect_GTot_lid))
               && (should_return env (FStar_Pervasives_Native.Some e) lc))
              &&
              (let uu____7073 =
                 FStar_TypeChecker_Common.is_lcomp_partial_return lc in
               Prims.op_Negation uu____7073) in
          let flags =
            if should_return1
            then
              let uu____7081 = FStar_TypeChecker_Common.is_total_lcomp lc in
              (if uu____7081
               then FStar_Syntax_Syntax.RETURN ::
                 (lc.FStar_TypeChecker_Common.cflags)
               else FStar_Syntax_Syntax.PARTIAL_RETURN ::
                 (lc.FStar_TypeChecker_Common.cflags))
            else lc.FStar_TypeChecker_Common.cflags in
          let refine uu____7101 =
            let uu____7102 = FStar_TypeChecker_Common.lcomp_comp lc in
            match uu____7102 with
            | (c, g_c) ->
                let u_t =
                  match comp_univ_opt c with
                  | FStar_Pervasives_Native.Some u_t -> u_t
                  | FStar_Pervasives_Native.None ->
                      env.FStar_TypeChecker_Env.universe_of env
                        (FStar_Syntax_Util.comp_result c) in
                let m =
                  let uu____7118 =
                    FStar_All.pipe_right m_opt FStar_Util.is_none in
                  if uu____7118
                  then FStar_Parser_Const.effect_PURE_lid
                  else
                    (let uu____7126 =
                       let uu____7128 =
                         FStar_All.pipe_right c
                           FStar_Syntax_Util.comp_effect_name in
                       FStar_All.pipe_right uu____7128 (is_pure_effect env) in
                     if uu____7126
                     then FStar_All.pipe_right m_opt FStar_Util.must
                     else FStar_Parser_Const.effect_PURE_lid) in
                let uu____7137 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____7137
                then
                  let uu____7146 =
                    return_value env m (FStar_Pervasives_Native.Some u_t)
                      (FStar_Syntax_Util.comp_result c) e in
                  (match uu____7146 with
                   | (retc, g_retc) ->
                       let g_c1 = FStar_TypeChecker_Env.conj_guard g_c g_retc in
                       let uu____7160 =
                         let uu____7162 = FStar_Syntax_Util.is_pure_comp c in
                         Prims.op_Negation uu____7162 in
                       if uu____7160
                       then
                         let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                         let retc2 =
                           let uu___910_7173 = retc1 in
                           {
                             FStar_Syntax_Syntax.comp_univs =
                               (uu___910_7173.FStar_Syntax_Syntax.comp_univs);
                             FStar_Syntax_Syntax.effect_name =
                               FStar_Parser_Const.effect_GHOST_lid;
                             FStar_Syntax_Syntax.result_typ =
                               (uu___910_7173.FStar_Syntax_Syntax.result_typ);
                             FStar_Syntax_Syntax.effect_args =
                               (uu___910_7173.FStar_Syntax_Syntax.effect_args);
                             FStar_Syntax_Syntax.flags = flags
                           } in
                         let uu____7174 = FStar_Syntax_Syntax.mk_Comp retc2 in
                         (uu____7174, g_c1)
                       else
                         (let uu____7181 =
                            FStar_Syntax_Util.comp_set_flags retc flags in
                          (uu____7181, g_c1)))
                else
                  (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                   let t = c1.FStar_Syntax_Syntax.result_typ in
                   let c2 = FStar_Syntax_Syntax.mk_Comp c1 in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (t.FStar_Syntax_Syntax.pos)) t in
                   let xexp = FStar_Syntax_Syntax.bv_to_name x in
                   let env_x = FStar_TypeChecker_Env.push_bv env x in
                   let uu____7196 =
                     return_value env_x m (FStar_Pervasives_Native.Some u_t)
                       t xexp in
                   match uu____7196 with
                   | (ret, g_ret) ->
                       let ret1 =
                         let uu____7210 =
                           FStar_Syntax_Util.comp_set_flags ret
                             [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                         FStar_All.pipe_left
                           FStar_TypeChecker_Common.lcomp_of_comp uu____7210 in
                       let eq = FStar_Syntax_Util.mk_eq2 u_t t xexp e in
                       let eq_ret =
                         weaken_precondition env_x ret1
                           (FStar_TypeChecker_Common.NonTrivial eq) in
                       let uu____7213 =
                         let uu____7218 =
                           let uu____7219 =
                             FStar_TypeChecker_Common.lcomp_of_comp c2 in
                           bind e.FStar_Syntax_Syntax.pos env
                             FStar_Pervasives_Native.None uu____7219
                             ((FStar_Pervasives_Native.Some x), eq_ret) in
                         FStar_TypeChecker_Common.lcomp_comp uu____7218 in
                       (match uu____7213 with
                        | (bind_c, g_bind) ->
                            let uu____7230 =
                              FStar_Syntax_Util.comp_set_flags bind_c flags in
                            let uu____7233 =
                              FStar_TypeChecker_Env.conj_guards
                                [g_c; g_ret; g_bind] in
                            (uu____7230, uu____7233))) in
          if Prims.op_Negation should_return1
          then lc
          else
            FStar_TypeChecker_Common.mk_lcomp
              lc.FStar_TypeChecker_Common.eff_name
              lc.FStar_TypeChecker_Common.res_typ flags refine
let (maybe_assume_result_eq_pure_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env ->
    fun e ->
      fun lc ->
        maybe_assume_result_eq_pure_term_in_m env
          FStar_Pervasives_Native.None e lc
let (maybe_return_e2_and_bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Common.lcomp ->
          FStar_Syntax_Syntax.term ->
            lcomp_with_binder -> FStar_TypeChecker_Common.lcomp)
  =
  fun r ->
    fun env ->
      fun e1opt ->
        fun lc1 ->
          fun e2 ->
            fun uu____7287 ->
              match uu____7287 with
              | (x, lc2) ->
                  let lc21 =
                    let eff1 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc1.FStar_TypeChecker_Common.eff_name in
                    let eff2 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc2.FStar_TypeChecker_Common.eff_name in
                    let uu____7299 =
                      ((let uu____7303 = is_pure_or_ghost_effect env eff1 in
                        Prims.op_Negation uu____7303) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2) in
                    if uu____7299
                    then
                      let env_x =
                        match x with
                        | FStar_Pervasives_Native.None -> env
                        | FStar_Pervasives_Native.Some x1 ->
                            FStar_TypeChecker_Env.push_bv env x1 in
                      let uu____7308 =
                        FStar_All.pipe_right eff1
                          (fun uu____7313 ->
                             FStar_Pervasives_Native.Some uu____7313) in
                      maybe_assume_result_eq_pure_term_in_m env_x uu____7308
                        e2 lc2
                    else lc2 in
                  bind r env e1opt lc1 (x, lc21)
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun lid ->
      let uu____7329 =
        let uu____7330 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____7330 in
      FStar_Syntax_Syntax.fvar uu____7329 FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
let (mk_layered_conjunction :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.typ ->
            FStar_Syntax_Syntax.comp_typ ->
              FStar_Syntax_Syntax.comp_typ ->
                FStar_Range.range ->
                  (FStar_Syntax_Syntax.comp *
                    FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun ed ->
      fun u_a ->
        fun a ->
          fun p ->
            fun ct1 ->
              fun ct2 ->
                fun r ->
                  let conjunction_name =
                    let uu____7382 =
                      FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                    FStar_Util.format1 "%s.conjunction" uu____7382 in
                  let uu____7385 =
                    let uu____7390 =
                      let uu____7391 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator in
                      FStar_All.pipe_right uu____7391 FStar_Util.must in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7390 [u_a] in
                  match uu____7385 with
                  | (uu____7402, conjunction) ->
                      let uu____7404 =
                        let uu____7413 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args in
                        let uu____7428 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args in
                        (uu____7413, uu____7428) in
                      (match uu____7404 with
                       | (is1, is2) ->
                           let conjunction_t_error s =
                             let uu____7474 =
                               let uu____7476 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction in
                               FStar_Util.format3
                                 "conjunction %s (%s) does not have proper shape (reason:%s)"
                                 uu____7476 conjunction_name s in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7474) in
                           let uu____7480 =
                             let uu____7525 =
                               let uu____7526 =
                                 FStar_Syntax_Subst.compress conjunction in
                               uu____7526.FStar_Syntax_Syntax.n in
                             match uu____7525 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs, body, uu____7575) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____7607 =
                                   FStar_Syntax_Subst.open_term bs body in
                                 (match uu____7607 with
                                  | (a_b::bs1, body1) ->
                                      let uu____7679 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1 in
                                      (match uu____7679 with
                                       | (rest_bs, f_b::g_b::p_b::[]) ->
                                           let uu____7827 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____7827)))
                             | uu____7860 ->
                                 let uu____7861 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders" in
                                 FStar_Errors.raise_error uu____7861 r in
                           (match uu____7480 with
                            | (a_b, rest_bs, f_b, g_b, p_b, body) ->
                                let uu____7986 =
                                  let uu____7993 =
                                    let uu____7994 =
                                      let uu____7995 =
                                        let uu____8002 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst in
                                        (uu____8002, a) in
                                      FStar_Syntax_Syntax.NT uu____7995 in
                                    [uu____7994] in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____7993
                                    (fun b ->
                                       let uu____8018 =
                                         FStar_Syntax_Print.binder_to_string
                                           b in
                                       let uu____8020 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname in
                                       let uu____8022 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____8018 uu____8020 uu____8022) r in
                                (match uu____7986 with
                                 | (rest_bs_uvars, g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b ->
                                            fun t ->
                                              let uu____8060 =
                                                let uu____8067 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst in
                                                (uu____8067, t) in
                                              FStar_Syntax_Syntax.NT
                                                uu____8060) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p])) in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____8106 =
                                           let uu____8107 =
                                             let uu____8110 =
                                               let uu____8111 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst in
                                               uu____8111.FStar_Syntax_Syntax.sort in
                                             FStar_Syntax_Subst.compress
                                               uu____8110 in
                                           uu____8107.FStar_Syntax_Syntax.n in
                                         match uu____8106 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8122, uu____8123::is) ->
                                             let uu____8165 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst) in
                                             FStar_All.pipe_right uu____8165
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8198 ->
                                             let uu____8199 =
                                               conjunction_t_error
                                                 "f's type is not a repr type" in
                                             FStar_Errors.raise_error
                                               uu____8199 r in
                                       FStar_List.fold_left2
                                         (fun g ->
                                            fun i1 ->
                                              fun f_i ->
                                                let uu____8215 =
                                                  FStar_TypeChecker_Rel.layered_effect_teq
                                                    env i1 f_i
                                                    (FStar_Pervasives_Native.Some
                                                       conjunction_name) in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8215)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____8221 =
                                           let uu____8222 =
                                             let uu____8225 =
                                               let uu____8226 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst in
                                               uu____8226.FStar_Syntax_Syntax.sort in
                                             FStar_Syntax_Subst.compress
                                               uu____8225 in
                                           uu____8222.FStar_Syntax_Syntax.n in
                                         match uu____8221 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8237, uu____8238::is) ->
                                             let uu____8280 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst) in
                                             FStar_All.pipe_right uu____8280
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8313 ->
                                             let uu____8314 =
                                               conjunction_t_error
                                                 "g's type is not a repr type" in
                                             FStar_Errors.raise_error
                                               uu____8314 r in
                                       FStar_List.fold_left2
                                         (fun g ->
                                            fun i2 ->
                                              fun g_i ->
                                                let uu____8330 =
                                                  FStar_TypeChecker_Rel.layered_effect_teq
                                                    env i2 g_i
                                                    (FStar_Pervasives_Native.Some
                                                       conjunction_name) in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8330)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body in
                                     let is =
                                       let uu____8336 =
                                         let uu____8337 =
                                           FStar_Syntax_Subst.compress body1 in
                                         uu____8337.FStar_Syntax_Syntax.n in
                                       match uu____8336 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8342, a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8397 ->
                                           let uu____8398 =
                                             conjunction_t_error
                                               "body is not a repr type" in
                                           FStar_Errors.raise_error
                                             uu____8398 r in
                                     let uu____8407 =
                                       let uu____8408 =
                                         let uu____8409 =
                                           FStar_All.pipe_right is
                                             (FStar_List.map
                                                FStar_Syntax_Syntax.as_arg) in
                                         {
                                           FStar_Syntax_Syntax.comp_univs =
                                             [u_a];
                                           FStar_Syntax_Syntax.effect_name =
                                             (ed.FStar_Syntax_Syntax.mname);
                                           FStar_Syntax_Syntax.result_typ = a;
                                           FStar_Syntax_Syntax.effect_args =
                                             uu____8409;
                                           FStar_Syntax_Syntax.flags = []
                                         } in
                                       FStar_Syntax_Syntax.mk_Comp uu____8408 in
                                     let uu____8432 =
                                       let uu____8433 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8433 g_guard in
                                     (uu____8407, uu____8432))))
let (mk_non_layered_conjunction :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.typ ->
            FStar_Syntax_Syntax.comp_typ ->
              FStar_Syntax_Syntax.comp_typ ->
                FStar_Range.range ->
                  (FStar_Syntax_Syntax.comp *
                    FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun ed ->
      fun u_a ->
        fun a ->
          fun p ->
            fun ct1 ->
              fun ct2 ->
                fun uu____8478 ->
                  let if_then_else =
                    let uu____8484 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator in
                    FStar_All.pipe_right uu____8484 FStar_Util.must in
                  let uu____8491 = destruct_wp_comp ct1 in
                  match uu____8491 with
                  | (uu____8502, uu____8503, wp_t) ->
                      let uu____8505 = destruct_wp_comp ct2 in
                      (match uu____8505 with
                       | (uu____8516, uu____8517, wp_e) ->
                           let wp =
                             let uu____8520 =
                               FStar_TypeChecker_Env.inst_effect_fun_with
                                 [u_a] env ed if_then_else in
                             let uu____8521 =
                               let uu____8522 = FStar_Syntax_Syntax.as_arg a in
                               let uu____8531 =
                                 let uu____8542 =
                                   FStar_Syntax_Syntax.as_arg p in
                                 let uu____8551 =
                                   let uu____8562 =
                                     FStar_Syntax_Syntax.as_arg wp_t in
                                   let uu____8571 =
                                     let uu____8582 =
                                       FStar_Syntax_Syntax.as_arg wp_e in
                                     [uu____8582] in
                                   uu____8562 :: uu____8571 in
                                 uu____8542 :: uu____8551 in
                               uu____8522 :: uu____8531 in
                             let uu____8631 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Syntax.mk_Tm_app uu____8520
                               uu____8521 uu____8631 in
                           let uu____8632 = mk_comp ed u_a a wp [] in
                           (uu____8632, FStar_TypeChecker_Env.trivial_guard))
let (comp_pure_wp_false :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun u ->
      fun t ->
        let post_k =
          let uu____8652 =
            let uu____8661 = FStar_Syntax_Syntax.null_binder t in
            [uu____8661] in
          let uu____8680 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
          FStar_Syntax_Util.arrow uu____8652 uu____8680 in
        let kwp =
          let uu____8686 =
            let uu____8695 = FStar_Syntax_Syntax.null_binder post_k in
            [uu____8695] in
          let uu____8714 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
          FStar_Syntax_Util.arrow uu____8686 uu____8714 in
        let post =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k in
        let wp =
          let uu____8721 =
            let uu____8722 = FStar_Syntax_Syntax.mk_binder post in
            [uu____8722] in
          let uu____8741 = fvar_const env FStar_Parser_Const.false_lid in
          FStar_Syntax_Util.abs uu____8721 uu____8741
            (FStar_Pervasives_Native.Some
               (FStar_Syntax_Util.mk_residual_comp
                  FStar_Parser_Const.effect_Tot_lid
                  FStar_Pervasives_Native.None [FStar_Syntax_Syntax.TOTAL])) in
        let md =
          FStar_TypeChecker_Env.get_effect_decl env
            FStar_Parser_Const.effect_PURE_lid in
        mk_comp md u t wp []
let (bind_cases :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ * FStar_Ident.lident *
        FStar_Syntax_Syntax.cflag Prims.list *
        (Prims.bool -> FStar_TypeChecker_Common.lcomp)) Prims.list ->
        FStar_Syntax_Syntax.bv -> FStar_TypeChecker_Common.lcomp)
  =
  fun env0 ->
    fun res_t ->
      fun lcases ->
        fun scrutinee ->
          let env =
            let uu____8800 =
              let uu____8801 =
                FStar_All.pipe_right scrutinee FStar_Syntax_Syntax.mk_binder in
              [uu____8801] in
            FStar_TypeChecker_Env.push_binders env0 uu____8800 in
          let eff =
            FStar_List.fold_left
              (fun eff ->
                 fun uu____8848 ->
                   match uu____8848 with
                   | (uu____8862, eff_label, uu____8864, uu____8865) ->
                       join_effects env eff eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases in
          let uu____8878 =
            let uu____8886 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu____8924 ->
                      match uu____8924 with
                      | (uu____8939, uu____8940, flags, uu____8942) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___5_8959 ->
                                  match uu___5_8959 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE ->
                                      true
                                  | uu____8962 -> false)))) in
            if uu____8886
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, []) in
          match uu____8878 with
          | (should_not_inline_whole_match, bind_cases_flags) ->
              let bind_cases uu____8999 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
                let uu____9001 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
                if uu____9001
                then
                  let uu____9008 = lax_mk_tot_or_comp_l eff u_res_t res_t [] in
                  (uu____9008, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let maybe_return eff_label_then cthen =
                     let uu____9029 =
                       should_not_inline_whole_match ||
                         (let uu____9032 = is_pure_or_ghost_effect env eff in
                          Prims.op_Negation uu____9032) in
                     if uu____9029 then cthen true else cthen false in
                   let uu____9039 =
                     let uu____9050 =
                       let uu____9063 =
                         let uu____9068 =
                           let uu____9079 =
                             FStar_All.pipe_right lcases
                               (FStar_List.map
                                  (fun uu____9129 ->
                                     match uu____9129 with
                                     | (g, uu____9148, uu____9149,
                                        uu____9150) -> g)) in
                           FStar_All.pipe_right uu____9079
                             (FStar_List.fold_left
                                (fun uu____9198 ->
                                   fun g ->
                                     match uu____9198 with
                                     | (conds, acc) ->
                                         let cond =
                                           let uu____9239 =
                                             FStar_Syntax_Util.mk_neg g in
                                           FStar_Syntax_Util.mk_conj acc
                                             uu____9239 in
                                         ((FStar_List.append conds [cond]),
                                           cond))
                                ([FStar_Syntax_Util.t_true],
                                  FStar_Syntax_Util.t_true)) in
                         FStar_All.pipe_right uu____9068
                           FStar_Pervasives_Native.fst in
                       FStar_All.pipe_right uu____9063
                         (fun l ->
                            FStar_List.splitAt
                              ((FStar_List.length l) - Prims.int_one) l) in
                     FStar_All.pipe_right uu____9050
                       (fun uu____9337 ->
                          match uu____9337 with
                          | (l1, l2) ->
                              let uu____9378 = FStar_List.hd l2 in
                              (l1, uu____9378)) in
                   match uu____9039 with
                   | (neg_branch_conds, exhaustiveness_branch_cond) ->
                       let uu____9407 =
                         match lcases with
                         | [] ->
                             let uu____9438 =
                               comp_pure_wp_false env u_res_t res_t in
                             (FStar_Pervasives_Native.None, uu____9438,
                               FStar_TypeChecker_Env.trivial_guard)
                         | uu____9441 ->
                             let uu____9458 =
                               let uu____9491 =
                                 let uu____9502 =
                                   FStar_All.pipe_right neg_branch_conds
                                     (FStar_List.splitAt
                                        ((FStar_List.length lcases) -
                                           Prims.int_one)) in
                                 FStar_All.pipe_right uu____9502
                                   (fun uu____9574 ->
                                      match uu____9574 with
                                      | (l1, l2) ->
                                          let uu____9615 = FStar_List.hd l2 in
                                          (l1, uu____9615)) in
                               match uu____9491 with
                               | (neg_branch_conds1, neg_last) ->
                                   let uu____9672 =
                                     let uu____9711 =
                                       FStar_All.pipe_right lcases
                                         (FStar_List.splitAt
                                            ((FStar_List.length lcases) -
                                               Prims.int_one)) in
                                     FStar_All.pipe_right uu____9711
                                       (fun uu____9923 ->
                                          match uu____9923 with
                                          | (l1, l2) ->
                                              let uu____10074 =
                                                FStar_List.hd l2 in
                                              (l1, uu____10074)) in
                                   (match uu____9672 with
                                    | (lcases1,
                                       (g_last, eff_last, uu____10176,
                                        c_last)) ->
                                        let uu____10246 =
                                          let lc =
                                            maybe_return eff_last c_last in
                                          let uu____10252 =
                                            FStar_TypeChecker_Common.lcomp_comp
                                              lc in
                                          match uu____10252 with
                                          | (c, g) ->
                                              let uu____10263 =
                                                let uu____10264 =
                                                  FStar_Syntax_Util.mk_conj
                                                    g_last neg_last in
                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                  g uu____10264 in
                                              (c, uu____10263) in
                                        (match uu____10246 with
                                         | (c, g) ->
                                             let uu____10299 =
                                               let uu____10300 =
                                                 FStar_All.pipe_right
                                                   eff_last
                                                   (FStar_TypeChecker_Env.norm_eff_name
                                                      env) in
                                               FStar_All.pipe_right
                                                 uu____10300
                                                 (FStar_TypeChecker_Env.get_effect_decl
                                                    env) in
                                             (lcases1, neg_branch_conds1,
                                               uu____10299, c, g))) in
                             (match uu____9458 with
                              | (lcases1, neg_branch_conds1, md, comp,
                                 g_comp) ->
                                  FStar_List.fold_right2
                                    (fun uu____10432 ->
                                       fun neg_cond ->
                                         fun uu____10434 ->
                                           match (uu____10432, uu____10434)
                                           with
                                           | ((g, eff_label, uu____10494,
                                               cthen),
                                              (uu____10496, celse, g_comp1))
                                               ->
                                               let uu____10543 =
                                                 let uu____10548 =
                                                   maybe_return eff_label
                                                     cthen in
                                                 FStar_TypeChecker_Common.lcomp_comp
                                                   uu____10548 in
                                               (match uu____10543 with
                                                | (cthen1, g_then) ->
                                                    let uu____10559 =
                                                      let uu____10570 =
                                                        lift_comps_sep_guards
                                                          env cthen1 celse
                                                          FStar_Pervasives_Native.None
                                                          false in
                                                      match uu____10570 with
                                                      | (m, cthen2, celse1,
                                                         g_lift_then,
                                                         g_lift_else) ->
                                                          let md1 =
                                                            FStar_TypeChecker_Env.get_effect_decl
                                                              env m in
                                                          let uu____10598 =
                                                            FStar_All.pipe_right
                                                              cthen2
                                                              FStar_Syntax_Util.comp_to_comp_typ in
                                                          let uu____10599 =
                                                            FStar_All.pipe_right
                                                              celse1
                                                              FStar_Syntax_Util.comp_to_comp_typ in
                                                          (md1, uu____10598,
                                                            uu____10599,
                                                            g_lift_then,
                                                            g_lift_else) in
                                                    (match uu____10559 with
                                                     | (md1, ct_then,
                                                        ct_else, g_lift_then,
                                                        g_lift_else) ->
                                                         let fn =
                                                           let uu____10650 =
                                                             FStar_All.pipe_right
                                                               md1
                                                               FStar_Syntax_Util.is_layered in
                                                           if uu____10650
                                                           then
                                                             mk_layered_conjunction
                                                           else
                                                             mk_non_layered_conjunction in
                                                         let uu____10684 =
                                                           let uu____10689 =
                                                             FStar_TypeChecker_Env.get_range
                                                               env in
                                                           fn env md1 u_res_t
                                                             res_t g ct_then
                                                             ct_else
                                                             uu____10689 in
                                                         (match uu____10684
                                                          with
                                                          | (c,
                                                             g_conjunction)
                                                              ->
                                                              let g_then1 =
                                                                let uu____10701
                                                                  =
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_then
                                                                    g_lift_then in
                                                                let uu____10702
                                                                  =
                                                                  FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    g in
                                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                                  uu____10701
                                                                  uu____10702 in
                                                              let g_else =
                                                                let uu____10704
                                                                  =
                                                                  let uu____10705
                                                                    =
                                                                    FStar_Syntax_Util.mk_neg
                                                                    g in
                                                                  FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    uu____10705 in
                                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                                  g_lift_else
                                                                  uu____10704 in
                                                              let uu____10708
                                                                =
                                                                FStar_TypeChecker_Env.conj_guards
                                                                  [g_comp1;
                                                                  g_then1;
                                                                  g_else;
                                                                  g_conjunction] in
                                                              ((FStar_Pervasives_Native.Some
                                                                  md1), c,
                                                                uu____10708)))))
                                    lcases1 neg_branch_conds1
                                    ((FStar_Pervasives_Native.Some md), comp,
                                      g_comp)) in
                       (match uu____9407 with
                        | (md, comp, g_comp) ->
                            let uu____10724 =
                              let uu____10729 =
                                let check =
                                  FStar_Syntax_Util.mk_imp
                                    exhaustiveness_branch_cond
                                    FStar_Syntax_Util.t_false in
                                let check1 =
                                  let uu____10736 =
                                    FStar_TypeChecker_Env.get_range env in
                                  label
                                    FStar_TypeChecker_Err.exhaustiveness_check
                                    uu____10736 check in
                                strengthen_comp env
                                  FStar_Pervasives_Native.None comp check1
                                  bind_cases_flags in
                              match uu____10729 with
                              | (c, g) ->
                                  let uu____10747 =
                                    FStar_TypeChecker_Env.conj_guard g_comp g in
                                  (c, uu____10747) in
                            (match uu____10724 with
                             | (comp1, g_comp1) ->
                                 let g_comp2 =
                                   let uu____10755 =
                                     let uu____10756 =
                                       FStar_All.pipe_right scrutinee
                                         FStar_Syntax_Syntax.mk_binder in
                                     [uu____10756] in
                                   FStar_TypeChecker_Env.close_guard env0
                                     uu____10755 g_comp1 in
                                 (match lcases with
                                  | [] -> (comp1, g_comp2)
                                  | uu____10799::[] -> (comp1, g_comp2)
                                  | uu____10842 ->
                                      let uu____10859 =
                                        let uu____10861 =
                                          FStar_All.pipe_right md
                                            FStar_Util.must in
                                        FStar_All.pipe_right uu____10861
                                          FStar_Syntax_Util.is_layered in
                                      if uu____10859
                                      then (comp1, g_comp2)
                                      else
                                        (let comp2 =
                                           FStar_TypeChecker_Env.comp_to_comp_typ
                                             env comp1 in
                                         let md1 =
                                           FStar_TypeChecker_Env.get_effect_decl
                                             env
                                             comp2.FStar_Syntax_Syntax.effect_name in
                                         let uu____10874 =
                                           destruct_wp_comp comp2 in
                                         match uu____10874 with
                                         | (uu____10885, uu____10886, wp) ->
                                             let ite_wp =
                                               let uu____10889 =
                                                 FStar_All.pipe_right md1
                                                   FStar_Syntax_Util.get_wp_ite_combinator in
                                               FStar_All.pipe_right
                                                 uu____10889 FStar_Util.must in
                                             let wp1 =
                                               let uu____10897 =
                                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                                   [u_res_t] env md1 ite_wp in
                                               let uu____10898 =
                                                 let uu____10899 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     res_t in
                                                 let uu____10908 =
                                                   let uu____10919 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp in
                                                   [uu____10919] in
                                                 uu____10899 :: uu____10908 in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu____10897 uu____10898
                                                 wp.FStar_Syntax_Syntax.pos in
                                             let uu____10952 =
                                               mk_comp md1 u_res_t res_t wp1
                                                 bind_cases_flags in
                                             (uu____10952, g_comp2)))))) in
              FStar_TypeChecker_Common.mk_lcomp eff res_t bind_cases_flags
                bind_cases
let (check_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      fun c ->
        fun c' ->
          let uu____10987 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____10987 with
          | FStar_Pervasives_Native.None ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____11003 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c' in
                let uu____11009 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error uu____11003 uu____11009
              else
                (let uu____11018 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c' in
                 let uu____11024 = FStar_TypeChecker_Env.get_range env in
                 FStar_Errors.raise_error uu____11018 uu____11024)
          | FStar_Pervasives_Native.Some g -> (e, c', g)
let (universe_of_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.universe)
  =
  fun env ->
    fun u_res ->
      fun c ->
        let c_lid =
          let uu____11049 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name in
          FStar_All.pipe_right uu____11049
            (FStar_TypeChecker_Env.norm_eff_name env) in
        let uu____11052 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid in
        if uu____11052
        then u_res
        else
          (let is_total =
             let uu____11059 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid in
             FStar_All.pipe_right uu____11059
               (FStar_List.existsb
                  (fun q -> q = FStar_Syntax_Syntax.TotalEffect)) in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____11070 = FStar_TypeChecker_Env.effect_repr env c u_res in
              match uu____11070 with
              | FStar_Pervasives_Native.None ->
                  let uu____11073 =
                    let uu____11079 =
                      let uu____11081 =
                        FStar_Syntax_Print.lid_to_string c_lid in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____11081 in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____11079) in
                  FStar_Errors.raise_error uu____11073
                    c.FStar_Syntax_Syntax.pos
              | FStar_Pervasives_Native.Some tm ->
                  env.FStar_TypeChecker_Env.universe_of env tm))
let (check_trivial_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp_typ * FStar_Syntax_Syntax.formula *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun c ->
      let ct =
        FStar_All.pipe_right c
          (FStar_TypeChecker_Env.unfold_effect_abbrev env) in
      let md =
        FStar_TypeChecker_Env.get_effect_decl env
          ct.FStar_Syntax_Syntax.effect_name in
      let uu____11105 = destruct_wp_comp ct in
      match uu____11105 with
      | (u_t, t, wp) ->
          let vc =
            let uu____11122 =
              let uu____11123 =
                let uu____11124 =
                  FStar_All.pipe_right md
                    FStar_Syntax_Util.get_wp_trivial_combinator in
                FStar_All.pipe_right uu____11124 FStar_Util.must in
              FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                uu____11123 in
            let uu____11131 =
              let uu____11132 = FStar_Syntax_Syntax.as_arg t in
              let uu____11141 =
                let uu____11152 = FStar_Syntax_Syntax.as_arg wp in
                [uu____11152] in
              uu____11132 :: uu____11141 in
            let uu____11185 = FStar_TypeChecker_Env.get_range env in
            FStar_Syntax_Syntax.mk_Tm_app uu____11122 uu____11131 uu____11185 in
          let uu____11186 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc) in
          (ct, vc, uu____11186)
let (coerce_with :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        FStar_Syntax_Syntax.typ ->
          FStar_Ident.lident ->
            FStar_Syntax_Syntax.universes ->
              FStar_Syntax_Syntax.args ->
                (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp) ->
                  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp))
  =
  fun env ->
    fun e ->
      fun lc ->
        fun ty ->
          fun f ->
            fun us ->
              fun eargs ->
                fun mkcomp ->
                  let uu____11241 =
                    FStar_TypeChecker_Env.try_lookup_lid env f in
                  match uu____11241 with
                  | FStar_Pervasives_Native.Some uu____11256 ->
                      ((let uu____11274 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions") in
                        if uu____11274
                        then
                          let uu____11278 = FStar_Ident.string_of_lid f in
                          FStar_Util.print1 "Coercing with %s!\n" uu____11278
                        else ());
                       (let coercion =
                          let uu____11284 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos in
                          FStar_Syntax_Syntax.fvar uu____11284
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs in
                        let lc1 =
                          let uu____11291 =
                            let uu____11292 =
                              let uu____11293 = mkcomp ty in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____11293 in
                            (FStar_Pervasives_Native.None, uu____11292) in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____11291 in
                        let e1 =
                          let uu____11297 =
                            let uu____11298 = FStar_Syntax_Syntax.as_arg e in
                            [uu____11298] in
                          FStar_Syntax_Syntax.mk_Tm_app coercion2 uu____11297
                            e.FStar_Syntax_Syntax.pos in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None ->
                      ((let uu____11332 =
                          let uu____11338 =
                            let uu____11340 = FStar_Ident.string_of_lid f in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____11340 in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____11338) in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____11332);
                       (e, lc))
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee ->
    match projectee with | Yes _0 -> true | uu____11359 -> false
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee -> match projectee with | Yes _0 -> _0
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee ->
    match projectee with | Maybe -> true | uu____11377 -> false
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee -> match projectee with | No -> true | uu____11388 -> false
let rec (check_erased :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> isErased) =
  fun env ->
    fun t ->
      let norm' =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
          FStar_TypeChecker_Env.Primops;
          FStar_TypeChecker_Env.Weak;
          FStar_TypeChecker_Env.HNF;
          FStar_TypeChecker_Env.Iota] in
      let t1 = norm' env t in
      let t2 = FStar_Syntax_Util.unrefine t1 in
      let uu____11412 = FStar_Syntax_Util.head_and_args t2 in
      match uu____11412 with
      | (h, args) ->
          let h1 = FStar_Syntax_Util.un_uinst h in
          let r =
            let uu____11457 =
              let uu____11472 =
                let uu____11473 = FStar_Syntax_Subst.compress h1 in
                uu____11473.FStar_Syntax_Syntax.n in
              (uu____11472, args) in
            match uu____11457 with
            | (FStar_Syntax_Syntax.Tm_fvar fv,
               (a, FStar_Pervasives_Native.None)::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____11520, uu____11521) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown, uu____11554) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match (uu____11575, branches),
               uu____11577) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc ->
                        fun br ->
                          match acc with
                          | Yes uu____11641 -> Maybe
                          | Maybe -> Maybe
                          | No ->
                              let uu____11642 =
                                FStar_Syntax_Subst.open_branch br in
                              (match uu____11642 with
                               | (uu____11643, uu____11644, br_body) ->
                                   let uu____11662 =
                                     let uu____11663 =
                                       let uu____11668 =
                                         let uu____11669 =
                                           let uu____11672 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names in
                                           FStar_All.pipe_right uu____11672
                                             FStar_Util.set_elements in
                                         FStar_All.pipe_right uu____11669
                                           (FStar_TypeChecker_Env.push_bvs
                                              env) in
                                       check_erased uu____11668 in
                                     FStar_All.pipe_right br_body uu____11663 in
                                   (match uu____11662 with
                                    | No -> No
                                    | uu____11683 -> Maybe))) No)
            | uu____11684 -> No in
          r
let (maybe_coerce_lc :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      fun lc ->
        fun exp_t ->
          let should_coerce =
            (((let uu____11736 = FStar_Options.use_two_phase_tc () in
               Prims.op_Negation uu____11736) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ()) in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
               let uu____11755 =
                 let uu____11756 = FStar_Syntax_Subst.compress t1 in
                 uu____11756.FStar_Syntax_Syntax.n in
               match uu____11755 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____11761 -> false in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
               let uu____11771 =
                 let uu____11772 = FStar_Syntax_Subst.compress t1 in
                 uu____11772.FStar_Syntax_Syntax.n in
               match uu____11771 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____11777 -> false in
             let is_type t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
               let t2 = FStar_Syntax_Util.unrefine t1 in
               let uu____11788 =
                 let uu____11789 = FStar_Syntax_Subst.compress t2 in
                 uu____11789.FStar_Syntax_Syntax.n in
               match uu____11788 with
               | FStar_Syntax_Syntax.Tm_type uu____11793 -> true
               | uu____11795 -> false in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ in
             let uu____11798 = FStar_Syntax_Util.head_and_args res_typ in
             match uu____11798 with
             | (head, args) ->
                 ((let uu____11848 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions") in
                   if uu____11848
                   then
                     let uu____11852 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                     let uu____11854 = FStar_Syntax_Print.term_to_string e in
                     let uu____11856 =
                       FStar_Syntax_Print.term_to_string res_typ in
                     let uu____11858 =
                       FStar_Syntax_Print.term_to_string exp_t in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____11852 uu____11854 uu____11856 uu____11858
                   else ());
                  (let mk_erased u t =
                     let uu____11876 =
                       let uu____11879 =
                         fvar_const env FStar_Parser_Const.erased_lid in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____11879 [u] in
                     let uu____11880 =
                       let uu____11891 = FStar_Syntax_Syntax.as_arg t in
                       [uu____11891] in
                     FStar_Syntax_Util.mk_app uu____11876 uu____11880 in
                   let uu____11916 =
                     let uu____11931 =
                       let uu____11932 = FStar_Syntax_Util.un_uinst head in
                       uu____11932.FStar_Syntax_Syntax.n in
                     (uu____11931, args) in
                   match uu____11916 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type exp_t)
                       ->
                       let uu____11970 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total in
                       (match uu____11970 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____12010 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac in
                       (match uu____12010 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____12050 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac in
                       (match uu____12050 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____12090 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac in
                       (match uu____12090 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____12111 ->
                       let uu____12126 =
                         let uu____12131 = check_erased env res_typ in
                         let uu____12132 = check_erased env exp_t in
                         (uu____12131, uu____12132) in
                       (match uu____12126 with
                        | (No, Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty in
                            let uu____12141 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty in
                            (match uu____12141 with
                             | FStar_Pervasives_Native.None ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e in
                                 let uu____12152 =
                                   let uu____12157 =
                                     let uu____12158 =
                                       FStar_Syntax_Syntax.iarg ty in
                                     [uu____12158] in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____12157
                                     FStar_Syntax_Syntax.mk_Total in
                                 (match uu____12152 with
                                  | (e1, lc1) -> (e1, lc1, g1)))
                        | (Yes ty, No) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty in
                            let uu____12193 =
                              let uu____12198 =
                                let uu____12199 = FStar_Syntax_Syntax.iarg ty in
                                [uu____12199] in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____12198
                                FStar_Syntax_Syntax.mk_GTotal in
                            (match uu____12193 with
                             | (e1, lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____12232 ->
                            (e, lc, FStar_TypeChecker_Env.trivial_guard)))))
let (coerce_views :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp)
          FStar_Pervasives_Native.option)
  =
  fun env ->
    fun e ->
      fun lc ->
        let rt = lc.FStar_TypeChecker_Common.res_typ in
        let rt1 = FStar_Syntax_Util.unrefine rt in
        let uu____12267 = FStar_Syntax_Util.head_and_args rt1 in
        match uu____12267 with
        | (hd, args) ->
            let uu____12316 =
              let uu____12331 =
                let uu____12332 = FStar_Syntax_Subst.compress hd in
                uu____12332.FStar_Syntax_Syntax.n in
              (uu____12331, args) in
            (match uu____12316 with
             | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____12370 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac in
                 FStar_All.pipe_left
                   (fun uu____12397 ->
                      FStar_Pervasives_Native.Some uu____12397) uu____12370
             | uu____12398 -> FStar_Pervasives_Native.None)
let (weaken_result_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      fun lc ->
        fun t ->
          (let uu____12451 =
             FStar_TypeChecker_Env.debug env FStar_Options.High in
           if uu____12451
           then
             let uu____12454 = FStar_Syntax_Print.term_to_string e in
             let uu____12456 = FStar_TypeChecker_Common.lcomp_to_string lc in
             let uu____12458 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____12454 uu____12456 uu____12458
           else ());
          (let use_eq =
             (env.FStar_TypeChecker_Env.use_eq_strict ||
                env.FStar_TypeChecker_Env.use_eq)
               ||
               (let uu____12468 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name in
                match uu____12468 with
                | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____12493 -> false) in
           let gopt =
             if use_eq
             then
               let uu____12519 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t in
               (uu____12519, false)
             else
               (let uu____12529 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t in
                (uu____12529, true)) in
           match gopt with
           | (FStar_Pervasives_Native.None, uu____12542) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____12554 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ in
                 FStar_Errors.raise_error uu____12554
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1409_12570 = lc in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1409_12570.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1409_12570.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1409_12570.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g, apply_guard) ->
               let uu____12577 = FStar_TypeChecker_Env.guard_form g in
               (match uu____12577 with
                | FStar_TypeChecker_Common.Trivial ->
                    let strengthen_trivial uu____12593 =
                      let uu____12594 =
                        FStar_TypeChecker_Common.lcomp_comp lc in
                      match uu____12594 with
                      | (c, g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c in
                          let set_result_typ c1 =
                            FStar_Syntax_Util.set_result_typ c1 t in
                          let uu____12614 =
                            let uu____12616 = FStar_Syntax_Util.eq_tm t res_t in
                            uu____12616 = FStar_Syntax_Util.Equal in
                          if uu____12614
                          then
                            ((let uu____12623 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____12623
                              then
                                let uu____12627 =
                                  FStar_Syntax_Print.term_to_string res_t in
                                let uu____12629 =
                                  FStar_Syntax_Print.term_to_string t in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____12627 uu____12629
                              else ());
                             (let uu____12634 = set_result_typ c in
                              (uu____12634, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____12641 ->
                                   true
                               | uu____12649 -> false in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t in
                               let uu____12657 =
                                 let uu____12662 =
                                   let uu____12663 =
                                     FStar_All.pipe_right c
                                       FStar_Syntax_Util.comp_effect_name in
                                   FStar_All.pipe_right uu____12663
                                     (FStar_TypeChecker_Env.norm_eff_name env) in
                                 let uu____12666 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env uu____12662
                                   (comp_univ_opt c) res_t uu____12666 in
                               match uu____12657 with
                               | (cret, gret) ->
                                   let lc1 =
                                     let uu____12676 =
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                         c in
                                     let uu____12677 =
                                       let uu____12678 =
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                           cret in
                                       ((FStar_Pervasives_Native.Some x),
                                         uu____12678) in
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (FStar_Pervasives_Native.Some e)
                                       uu____12676 uu____12677 in
                                   ((let uu____12682 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme in
                                     if uu____12682
                                     then
                                       let uu____12686 =
                                         FStar_Syntax_Print.term_to_string e in
                                       let uu____12688 =
                                         FStar_Syntax_Print.comp_to_string c in
                                       let uu____12690 =
                                         FStar_Syntax_Print.term_to_string t in
                                       let uu____12692 =
                                         FStar_TypeChecker_Common.lcomp_to_string
                                           lc1 in
                                       FStar_Util.print4
                                         "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                         uu____12686 uu____12688 uu____12690
                                         uu____12692
                                     else ());
                                    (let uu____12697 =
                                       FStar_TypeChecker_Common.lcomp_comp
                                         lc1 in
                                     match uu____12697 with
                                     | (c1, g_lc) ->
                                         let uu____12708 = set_result_typ c1 in
                                         let uu____12709 =
                                           FStar_TypeChecker_Env.conj_guards
                                             [g_c; gret; g_lc] in
                                         (uu____12708, uu____12709)))
                             else
                               ((let uu____12713 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____12713
                                 then
                                   let uu____12717 =
                                     FStar_Syntax_Print.term_to_string res_t in
                                   let uu____12719 =
                                     FStar_Syntax_Print.comp_to_string c in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____12717 uu____12719
                                 else ());
                                (let uu____12724 = set_result_typ c in
                                 (uu____12724, g_c)))) in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1448_12728 = g in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred_to_tac =
                          (uu___1448_12728.FStar_TypeChecker_Common.deferred_to_tac);
                        FStar_TypeChecker_Common.deferred =
                          (uu___1448_12728.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1448_12728.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1448_12728.FStar_TypeChecker_Common.implicits)
                      } in
                    let strengthen uu____12738 =
                      let uu____12739 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ()) in
                      if uu____12739
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f in
                         let uu____12749 =
                           let uu____12750 = FStar_Syntax_Subst.compress f1 in
                           uu____12750.FStar_Syntax_Syntax.n in
                         match uu____12749 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____12757,
                              {
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Tm_fvar fv;
                                FStar_Syntax_Syntax.pos = uu____12759;
                                FStar_Syntax_Syntax.vars = uu____12760;_},
                              uu____12761)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1464_12787 = lc in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1464_12787.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1464_12787.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1464_12787.FStar_TypeChecker_Common.comp_thunk)
                               } in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____12788 ->
                             let uu____12789 =
                               FStar_TypeChecker_Common.lcomp_comp lc in
                             (match uu____12789 with
                              | (c, g_c) ->
                                  ((let uu____12801 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme in
                                    if uu____12801
                                    then
                                      let uu____12805 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ in
                                      let uu____12807 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t in
                                      let uu____12809 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c in
                                      let uu____12811 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1 in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____12805 uu____12807 uu____12809
                                        uu____12811
                                    else ());
                                   (let u_t_opt = comp_univ_opt c in
                                    let x =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (t.FStar_Syntax_Syntax.pos)) t in
                                    let xexp =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____12821 =
                                      let uu____12826 =
                                        let uu____12827 =
                                          FStar_All.pipe_right c
                                            FStar_Syntax_Util.comp_effect_name in
                                        FStar_All.pipe_right uu____12827
                                          (FStar_TypeChecker_Env.norm_eff_name
                                             env) in
                                      return_value env uu____12826 u_t_opt t
                                        xexp in
                                    match uu____12821 with
                                    | (cret, gret) ->
                                        let guard =
                                          if apply_guard
                                          then
                                            let uu____12838 =
                                              let uu____12839 =
                                                FStar_Syntax_Syntax.as_arg
                                                  xexp in
                                              [uu____12839] in
                                            FStar_Syntax_Syntax.mk_Tm_app f1
                                              uu____12838
                                              f1.FStar_Syntax_Syntax.pos
                                          else f1 in
                                        let uu____12866 =
                                          let uu____12871 =
                                            FStar_All.pipe_left
                                              (fun uu____12892 ->
                                                 FStar_Pervasives_Native.Some
                                                   uu____12892)
                                              (FStar_TypeChecker_Err.subtyping_failed
                                                 env
                                                 lc.FStar_TypeChecker_Common.res_typ
                                                 t) in
                                          let uu____12893 =
                                            let uu____12894 =
                                              FStar_TypeChecker_Env.push_bvs
                                                env [x] in
                                            FStar_TypeChecker_Env.set_range
                                              uu____12894
                                              e.FStar_Syntax_Syntax.pos in
                                          let uu____12895 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              cret in
                                          let uu____12896 =
                                            FStar_All.pipe_left
                                              FStar_TypeChecker_Env.guard_of_guard_formula
                                              (FStar_TypeChecker_Common.NonTrivial
                                                 guard) in
                                          strengthen_precondition uu____12871
                                            uu____12893 e uu____12895
                                            uu____12896 in
                                        (match uu____12866 with
                                         | (eq_ret,
                                            _trivial_so_ok_to_discard) ->
                                             let x1 =
                                               let uu___1484_12904 = x in
                                               {
                                                 FStar_Syntax_Syntax.ppname =
                                                   (uu___1484_12904.FStar_Syntax_Syntax.ppname);
                                                 FStar_Syntax_Syntax.index =
                                                   (uu___1484_12904.FStar_Syntax_Syntax.index);
                                                 FStar_Syntax_Syntax.sort =
                                                   (lc.FStar_TypeChecker_Common.res_typ)
                                               } in
                                             let c1 =
                                               let uu____12906 =
                                                 FStar_TypeChecker_Common.lcomp_of_comp
                                                   c in
                                               bind e.FStar_Syntax_Syntax.pos
                                                 env
                                                 (FStar_Pervasives_Native.Some
                                                    e) uu____12906
                                                 ((FStar_Pervasives_Native.Some
                                                     x1), eq_ret) in
                                             let uu____12909 =
                                               FStar_TypeChecker_Common.lcomp_comp
                                                 c1 in
                                             (match uu____12909 with
                                              | (c2, g_lc) ->
                                                  ((let uu____12921 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        FStar_Options.Extreme in
                                                    if uu____12921
                                                    then
                                                      let uu____12925 =
                                                        FStar_TypeChecker_Normalize.comp_to_string
                                                          env c2 in
                                                      FStar_Util.print1
                                                        "Strengthened to %s\n"
                                                        uu____12925
                                                    else ());
                                                   (let uu____12930 =
                                                      FStar_TypeChecker_Env.conj_guards
                                                        [g_c; gret; g_lc] in
                                                    (c2, uu____12930))))))))) in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_12939 ->
                              match uu___6_12939 with
                              | FStar_Syntax_Syntax.RETURN ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____12942 -> [])) in
                    let lc1 =
                      let uu____12944 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name in
                      FStar_TypeChecker_Common.mk_lcomp uu____12944 t flags
                        strengthen in
                    let g2 =
                      let uu___1500_12946 = g1 in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred_to_tac =
                          (uu___1500_12946.FStar_TypeChecker_Common.deferred_to_tac);
                        FStar_TypeChecker_Common.deferred =
                          (uu___1500_12946.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1500_12946.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1500_12946.FStar_TypeChecker_Common.implicits)
                      } in
                    (e, lc1, g2)))
let (pure_or_ghost_pre_and_post :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option *
        FStar_Syntax_Syntax.typ))
  =
  fun env ->
    fun comp ->
      let mk_post_type res_t ens =
        let x = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t in
        let uu____12982 =
          let uu____12985 =
            let uu____12986 =
              let uu____12995 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_Syntax_Syntax.as_arg uu____12995 in
            [uu____12986] in
          FStar_Syntax_Syntax.mk_Tm_app ens uu____12985
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____12982 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t in
      let uu____13018 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____13018
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____13037 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____13053 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____13070 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid) in
             if uu____13070
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req, uu____13086)::(ens, uu____13088)::uu____13089 ->
                    let uu____13132 =
                      let uu____13135 = norm req in
                      FStar_Pervasives_Native.Some uu____13135 in
                    let uu____13136 =
                      let uu____13137 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____13137 in
                    (uu____13132, uu____13136)
                | uu____13140 ->
                    let uu____13151 =
                      let uu____13157 =
                        let uu____13159 =
                          FStar_Syntax_Print.comp_to_string comp in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____13159 in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____13157) in
                    FStar_Errors.raise_error uu____13151
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp, uu____13179)::uu____13180 ->
                    let uu____13207 =
                      let uu____13212 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____13212 in
                    (match uu____13207 with
                     | (us_r, uu____13244) ->
                         let uu____13245 =
                           let uu____13250 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____13250 in
                         (match uu____13245 with
                          | (us_e, uu____13282) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____13285 =
                                  let uu____13286 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r in
                                  FStar_Syntax_Syntax.fvar uu____13286
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____13285
                                  us_r in
                              let as_ens =
                                let uu____13288 =
                                  let uu____13289 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r in
                                  FStar_Syntax_Syntax.fvar uu____13289
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____13288
                                  us_e in
                              let req =
                                let uu____13291 =
                                  let uu____13292 =
                                    let uu____13303 =
                                      FStar_Syntax_Syntax.as_arg wp in
                                    [uu____13303] in
                                  ((ct1.FStar_Syntax_Syntax.result_typ),
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.imp_tag))
                                    :: uu____13292 in
                                FStar_Syntax_Syntax.mk_Tm_app as_req
                                  uu____13291
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____13341 =
                                  let uu____13342 =
                                    let uu____13353 =
                                      FStar_Syntax_Syntax.as_arg wp in
                                    [uu____13353] in
                                  ((ct1.FStar_Syntax_Syntax.result_typ),
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.imp_tag))
                                    :: uu____13342 in
                                FStar_Syntax_Syntax.mk_Tm_app as_ens
                                  uu____13341
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____13390 =
                                let uu____13393 = norm req in
                                FStar_Pervasives_Native.Some uu____13393 in
                              let uu____13394 =
                                let uu____13395 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____13395 in
                              (uu____13390, uu____13394)))
                | uu____13398 -> failwith "Impossible"))
let (reify_body :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun steps ->
      fun t ->
        let tm = FStar_Syntax_Util.mk_reify t in
        let tm' =
          FStar_TypeChecker_Normalize.normalize
            (FStar_List.append
               [FStar_TypeChecker_Env.Beta;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.Eager_unfolding;
               FStar_TypeChecker_Env.EraseUniverses;
               FStar_TypeChecker_Env.AllowUnboundUniverses;
               FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta]
               steps) env tm in
        (let uu____13437 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____13437
         then
           let uu____13442 = FStar_Syntax_Print.term_to_string tm in
           let uu____13444 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____13442
             uu____13444
         else ());
        tm'
let (reify_body_with_arg :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.arg -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun steps ->
      fun head ->
        fun arg ->
          let tm =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (head, [arg]))
              head.FStar_Syntax_Syntax.pos in
          let tm' =
            FStar_TypeChecker_Normalize.normalize
              (FStar_List.append
                 [FStar_TypeChecker_Env.Beta;
                 FStar_TypeChecker_Env.Reify;
                 FStar_TypeChecker_Env.Eager_unfolding;
                 FStar_TypeChecker_Env.EraseUniverses;
                 FStar_TypeChecker_Env.AllowUnboundUniverses;
                 FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta]
                 steps) env tm in
          (let uu____13503 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify") in
           if uu____13503
           then
             let uu____13508 = FStar_Syntax_Print.term_to_string tm in
             let uu____13510 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____13508
               uu____13510
           else ());
          tm'
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____13521 =
      let uu____13523 =
        let uu____13524 = FStar_Syntax_Subst.compress t in
        uu____13524.FStar_Syntax_Syntax.n in
      match uu____13523 with
      | FStar_Syntax_Syntax.Tm_app uu____13528 -> false
      | uu____13546 -> true in
    if uu____13521
    then t
    else
      (let uu____13551 = FStar_Syntax_Util.head_and_args t in
       match uu____13551 with
       | (head, args) ->
           let uu____13594 =
             let uu____13596 =
               let uu____13597 = FStar_Syntax_Subst.compress head in
               uu____13597.FStar_Syntax_Syntax.n in
             match uu____13596 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) ->
                 true
             | uu____13602 -> false in
           if uu____13594
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____13634 ->
                  failwith
                    "Impossible : Reify applied to multiple arguments after normalization.")
           else t)
let (maybe_instantiate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
          FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      fun t ->
        let torig = FStar_Syntax_Subst.compress t in
        if Prims.op_Negation env.FStar_TypeChecker_Env.instantiate_imp
        then (e, torig, FStar_TypeChecker_Env.trivial_guard)
        else
          ((let uu____13681 =
              FStar_TypeChecker_Env.debug env FStar_Options.High in
            if uu____13681
            then
              let uu____13684 = FStar_Syntax_Print.term_to_string e in
              let uu____13686 = FStar_Syntax_Print.term_to_string t in
              let uu____13688 =
                let uu____13690 = FStar_TypeChecker_Env.expected_typ env in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____13690 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____13684 uu____13686 uu____13688
            else ());
           (let unfolded_arrow_formals t1 =
              let rec aux bs t2 =
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf env t2 in
                let uu____13726 = FStar_Syntax_Util.arrow_formals t3 in
                match uu____13726 with
                | (bs', t4) ->
                    (match bs' with
                     | [] -> bs
                     | bs'1 -> aux (FStar_List.append bs bs'1) t4) in
              aux [] t1 in
            let number_of_implicits t1 =
              let formals = unfolded_arrow_formals t1 in
              let n_implicits =
                let uu____13760 =
                  FStar_All.pipe_right formals
                    (FStar_Util.prefix_until
                       (fun uu____13838 ->
                          match uu____13838 with
                          | (uu____13846, imp) ->
                              (FStar_Option.isNone imp) ||
                                (let uu____13853 =
                                   FStar_Syntax_Util.eq_aqual imp
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Equality) in
                                 uu____13853 = FStar_Syntax_Util.Equal))) in
                match uu____13760 with
                | FStar_Pervasives_Native.None -> FStar_List.length formals
                | FStar_Pervasives_Native.Some
                    (implicits, _first_explicit, _rest) ->
                    FStar_List.length implicits in
              n_implicits in
            let inst_n_binders t1 =
              let uu____13972 = FStar_TypeChecker_Env.expected_typ env in
              match uu____13972 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t in
                  let n_available = number_of_implicits t1 in
                  if n_available < n_expected
                  then
                    let uu____13986 =
                      let uu____13992 =
                        let uu____13994 = FStar_Util.string_of_int n_expected in
                        let uu____13996 = FStar_Syntax_Print.term_to_string e in
                        let uu____13998 =
                          FStar_Util.string_of_int n_available in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____13994 uu____13996 uu____13998 in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____13992) in
                    let uu____14002 = FStar_TypeChecker_Env.get_range env in
                    FStar_Errors.raise_error uu____13986 uu____14002
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected) in
            let decr_inst uu___7_14020 =
              match uu___7_14020 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one) in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                let uu____14063 = FStar_Syntax_Subst.open_comp bs c in
                (match uu____14063 with
                 | (bs1, c1) ->
                     let rec aux subst inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some uu____14194,
                          uu____14181) when uu____14194 = Prims.int_zero ->
                           ([], bs2, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____14227,
                          (x, FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit uu____14229))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort in
                           let uu____14263 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2 in
                           (match uu____14263 with
                            | (v, uu____14304, g) ->
                                ((let uu____14319 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High in
                                  if uu____14319
                                  then
                                    let uu____14322 =
                                      FStar_Syntax_Print.term_to_string v in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____14322
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst in
                                  let uu____14332 =
                                    aux subst1 (decr_inst inst_n) rest in
                                  match uu____14332 with
                                  | (args, bs3, subst2, g') ->
                                      let uu____14425 =
                                        FStar_TypeChecker_Env.conj_guard g g' in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____14425))))
                       | (uu____14452,
                          (x, FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tac_or_attr))::rest) ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort in
                           let meta_t =
                             match tac_or_attr with
                             | FStar_Syntax_Syntax.Arg_qualifier_meta_tac tau
                                 ->
                                 let uu____14491 =
                                   let uu____14498 = FStar_Dyn.mkdyn env in
                                   (uu____14498, tau) in
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   uu____14491
                             | FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                 attr ->
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_attr attr in
                           let uu____14504 =
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict
                               (FStar_Pervasives_Native.Some meta_t) in
                           (match uu____14504 with
                            | (v, uu____14545, g) ->
                                ((let uu____14560 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High in
                                  if uu____14560
                                  then
                                    let uu____14563 =
                                      FStar_Syntax_Print.term_to_string v in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____14563
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst in
                                  let uu____14573 =
                                    aux subst1 (decr_inst inst_n) rest in
                                  match uu____14573 with
                                  | (args, bs3, subst2, g') ->
                                      let uu____14666 =
                                        FStar_TypeChecker_Env.conj_guard g g' in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____14666))))
                       | (uu____14693, bs3) ->
                           ([], bs3, subst,
                             FStar_TypeChecker_Env.trivial_guard) in
                     let uu____14741 =
                       let uu____14768 = inst_n_binders t1 in
                       aux [] uu____14768 bs1 in
                     (match uu____14741 with
                      | (args, bs2, subst, guard) ->
                          (match (args, bs2) with
                           | ([], uu____14840) -> (e, torig, guard)
                           | (uu____14871, []) when
                               let uu____14902 =
                                 FStar_Syntax_Util.is_total_comp c1 in
                               Prims.op_Negation uu____14902 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____14904 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____14932 ->
                                     FStar_Syntax_Util.arrow bs2 c1 in
                               let t3 = FStar_Syntax_Subst.subst subst t2 in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   e.FStar_Syntax_Syntax.pos in
                               (e1, t3, guard))))
            | uu____14943 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs ->
    let uu____14955 =
      let uu____14959 = FStar_Util.set_elements univs in
      FStar_All.pipe_right uu____14959
        (FStar_List.map
           (fun u ->
              let uu____14971 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____14971 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____14955 (FStar_String.concat ", ")
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env ->
    fun x ->
      let uu____14999 = FStar_Util.set_is_empty x in
      if uu____14999
      then []
      else
        (let s =
           let uu____15019 =
             let uu____15022 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____15022 in
           FStar_All.pipe_right uu____15019 FStar_Util.set_elements in
         (let uu____15040 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____15040
          then
            let uu____15045 =
              let uu____15047 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____15047 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____15045
          else ());
         (let r =
            let uu____15056 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____15056 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____15101 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____15101
                     then
                       let uu____15106 =
                         let uu____15108 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____15108 in
                       let uu____15112 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____15114 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____15106 uu____15112 uu____15114
                     else ());
                    FStar_Syntax_Unionfind.univ_change u
                      (FStar_Syntax_Syntax.U_name u_name);
                    u_name)) in
          u_names))
let (gather_free_univnames :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env ->
    fun t ->
      let ctx_univnames = FStar_TypeChecker_Env.univnames env in
      let tm_univnames = FStar_Syntax_Free.univnames t in
      let univnames =
        let uu____15144 =
          FStar_Util.set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____15144 FStar_Util.set_elements in
      univnames
let (check_universe_generalization :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun explicit_univ_names ->
    fun generalized_univ_names ->
      fun t ->
        match (explicit_univ_names, generalized_univ_names) with
        | ([], uu____15183) -> generalized_univ_names
        | (uu____15190, []) -> explicit_univ_names
        | uu____15197 ->
            let uu____15206 =
              let uu____15212 =
                let uu____15214 = FStar_Syntax_Print.term_to_string t in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____15214 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____15212) in
            FStar_Errors.raise_error uu____15206 t.FStar_Syntax_Syntax.pos
let (generalize_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.tscheme)
  =
  fun env ->
    fun t0 ->
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.NoFullNorm;
          FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.DoNotUnfoldPureLets] env t0 in
      let univnames = gather_free_univnames env t in
      (let uu____15236 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____15236
       then
         let uu____15241 = FStar_Syntax_Print.term_to_string t in
         let uu____15243 = FStar_Syntax_Print.univ_names_to_string univnames in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____15241 uu____15243
       else ());
      (let univs = FStar_Syntax_Free.univs t in
       (let uu____15252 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____15252
        then
          let uu____15257 = string_of_univs univs in
          FStar_Util.print1 "univs to gen : %s\n" uu____15257
        else ());
       (let gen = gen_univs env univs in
        (let uu____15266 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen") in
         if uu____15266
         then
           let uu____15271 = FStar_Syntax_Print.term_to_string t in
           let uu____15273 = FStar_Syntax_Print.univ_names_to_string gen in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____15271 uu____15273
         else ());
        (let univs1 = check_universe_generalization univnames gen t0 in
         let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t in
         let ts = FStar_Syntax_Subst.close_univ_vars univs1 t1 in
         (univs1, ts))))
let (gen :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.comp) Prims.list ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_name
          Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_Syntax_Syntax.binder Prims.list) Prims.list
          FStar_Pervasives_Native.option)
  =
  fun env ->
    fun is_rec ->
      fun lecs ->
        let uu____15357 =
          let uu____15359 =
            FStar_Util.for_all
              (fun uu____15373 ->
                 match uu____15373 with
                 | (uu____15383, uu____15384, c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          FStar_All.pipe_left Prims.op_Negation uu____15359 in
        if uu____15357
        then FStar_Pervasives_Native.None
        else
          (let norm c =
             (let uu____15436 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              if uu____15436
              then
                let uu____15439 = FStar_Syntax_Print.comp_to_string c in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____15439
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c in
              (let uu____15446 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____15446
               then
                 let uu____15449 = FStar_Syntax_Print.comp_to_string c1 in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____15449
               else ());
              c1) in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu____15467 = FStar_Util.set_difference uvs env_uvars in
             FStar_All.pipe_right uu____15467 FStar_Util.set_elements in
           let univs_and_uvars_of_lec uu____15501 =
             match uu____15501 with
             | (lbname, e, c) ->
                 let c1 = norm c in
                 let t = FStar_Syntax_Util.comp_result c1 in
                 let univs = FStar_Syntax_Free.univs t in
                 let uvt = FStar_Syntax_Free.uvars t in
                 ((let uu____15538 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen") in
                   if uu____15538
                   then
                     let uu____15543 =
                       let uu____15545 =
                         let uu____15549 = FStar_Util.set_elements univs in
                         FStar_All.pipe_right uu____15549
                           (FStar_List.map
                              (fun u ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u))) in
                       FStar_All.pipe_right uu____15545
                         (FStar_String.concat ", ") in
                     let uu____15605 =
                       let uu____15607 =
                         let uu____15611 = FStar_Util.set_elements uvt in
                         FStar_All.pipe_right uu____15611
                           (FStar_List.map
                              (fun u ->
                                 let uu____15624 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head in
                                 let uu____15626 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                 FStar_Util.format2 "(%s : %s)" uu____15624
                                   uu____15626)) in
                       FStar_All.pipe_right uu____15607
                         (FStar_String.concat ", ") in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____15543
                       uu____15605
                   else ());
                  (let univs1 =
                     let uu____15640 = FStar_Util.set_elements uvt in
                     FStar_List.fold_left
                       (fun univs1 ->
                          fun uv ->
                            let uu____15652 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ in
                            FStar_Util.set_union univs1 uu____15652) univs
                       uu____15640 in
                   let uvs = gen_uvars uvt in
                   (let uu____15659 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen") in
                    if uu____15659
                    then
                      let uu____15664 =
                        let uu____15666 =
                          let uu____15670 = FStar_Util.set_elements univs1 in
                          FStar_All.pipe_right uu____15670
                            (FStar_List.map
                               (fun u ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u))) in
                        FStar_All.pipe_right uu____15666
                          (FStar_String.concat ", ") in
                      let uu____15726 =
                        let uu____15728 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u ->
                                  let uu____15742 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head in
                                  let uu____15744 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                  FStar_Util.format2 "(%s : %s)" uu____15742
                                    uu____15744)) in
                        FStar_All.pipe_right uu____15728
                          (FStar_String.concat ", ") in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____15664 uu____15726
                    else ());
                   (univs1, uvs, (lbname, e, c1)))) in
           let uu____15765 =
             let uu____15782 = FStar_List.hd lecs in
             univs_and_uvars_of_lec uu____15782 in
           match uu____15765 with
           | (univs, uvs, lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____15872 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1) in
                 if uu____15872
                 then ()
                 else
                   (let uu____15877 = lec_hd in
                    match uu____15877 with
                    | (lb1, uu____15885, uu____15886) ->
                        let uu____15887 = lec2 in
                        (match uu____15887 with
                         | (lb2, uu____15895, uu____15896) ->
                             let msg =
                               let uu____15899 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____15901 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____15899 uu____15901 in
                             let uu____15904 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____15904)) in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun u ->
                           FStar_All.pipe_right u21
                             (FStar_Util.for_some
                                (fun u' ->
                                   FStar_Syntax_Unionfind.equiv
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                     u'.FStar_Syntax_Syntax.ctx_uvar_head)))) in
                 let uu____15972 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1) in
                 if uu____15972
                 then ()
                 else
                   (let uu____15977 = lec_hd in
                    match uu____15977 with
                    | (lb1, uu____15985, uu____15986) ->
                        let uu____15987 = lec2 in
                        (match uu____15987 with
                         | (lb2, uu____15995, uu____15996) ->
                             let msg =
                               let uu____15999 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____16001 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____15999 uu____16001 in
                             let uu____16004 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____16004)) in
               let lecs1 =
                 let uu____16015 = FStar_List.tl lecs in
                 FStar_List.fold_right
                   (fun this_lec ->
                      fun lecs1 ->
                        let uu____16068 = univs_and_uvars_of_lec this_lec in
                        match uu____16068 with
                        | (this_univs, this_uvs, this_lec1) ->
                            (force_univs_eq this_lec1 univs this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____16015 [] in
               let lecs2 = lec_hd :: lecs1 in
               let gen_types uvs1 =
                 let fail rng k =
                   let uu____16178 = lec_hd in
                   match uu____16178 with
                   | (lbname, e, c) ->
                       let uu____16188 =
                         let uu____16194 =
                           let uu____16196 =
                             FStar_Syntax_Print.term_to_string k in
                           let uu____16198 =
                             FStar_Syntax_Print.lbname_to_string lbname in
                           let uu____16200 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c) in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____16196 uu____16198 uu____16200 in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____16194) in
                       FStar_Errors.raise_error uu____16188 rng in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u ->
                         let uu____16222 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head in
                         match uu____16222 with
                         | FStar_Pervasives_Native.Some uu____16231 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____16239 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ in
                             let uu____16243 =
                               FStar_Syntax_Util.arrow_formals k in
                             (match uu____16243 with
                              | (bs, kres) ->
                                  ((let uu____16263 =
                                      let uu____16264 =
                                        let uu____16267 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres in
                                        FStar_Syntax_Util.unrefine
                                          uu____16267 in
                                      uu____16264.FStar_Syntax_Syntax.n in
                                    match uu____16263 with
                                    | FStar_Syntax_Syntax.Tm_type uu____16268
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres in
                                        let uu____16272 =
                                          let uu____16274 =
                                            FStar_Util.set_is_empty free in
                                          Prims.op_Negation uu____16274 in
                                        if uu____16272
                                        then
                                          fail
                                            u.FStar_Syntax_Syntax.ctx_uvar_range
                                            kres
                                        else ()
                                    | uu____16279 ->
                                        fail
                                          u.FStar_Syntax_Syntax.ctx_uvar_range
                                          kres);
                                   (let a =
                                      let uu____16281 =
                                        let uu____16284 =
                                          FStar_TypeChecker_Env.get_range env in
                                        FStar_All.pipe_left
                                          (fun uu____16287 ->
                                             FStar_Pervasives_Native.Some
                                               uu____16287) uu____16284 in
                                      FStar_Syntax_Syntax.new_bv uu____16281
                                        kres in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____16295 ->
                                          let uu____16296 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Util.abs bs
                                            uu____16296
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_tot
                                                  kres)) in
                                    FStar_Syntax_Util.set_uvar
                                      u.FStar_Syntax_Syntax.ctx_uvar_head t;
                                    (a,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))))) in
               let gen_univs1 = gen_univs env univs in
               let gen_tvars = gen_types uvs in
               let ecs =
                 FStar_All.pipe_right lecs2
                   (FStar_List.map
                      (fun uu____16399 ->
                         match uu____16399 with
                         | (lbname, e, c) ->
                             let uu____16445 =
                               match (gen_tvars, gen_univs1) with
                               | ([], []) -> (e, c, [])
                               | uu____16506 ->
                                   let uu____16519 = (e, c) in
                                   (match uu____16519 with
                                    | (e0, c0) ->
                                        let c1 =
                                          FStar_TypeChecker_Normalize.normalize_comp
                                            [FStar_TypeChecker_Env.Beta;
                                            FStar_TypeChecker_Env.DoNotUnfoldPureLets;
                                            FStar_TypeChecker_Env.CompressUvars;
                                            FStar_TypeChecker_Env.NoFullNorm;
                                            FStar_TypeChecker_Env.Exclude
                                              FStar_TypeChecker_Env.Zeta] env
                                            c in
                                        let e1 =
                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                            env e in
                                        let e2 =
                                          if is_rec
                                          then
                                            let tvar_args =
                                              FStar_List.map
                                                (fun uu____16559 ->
                                                   match uu____16559 with
                                                   | (x, uu____16565) ->
                                                       let uu____16566 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____16566)
                                                gen_tvars in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____16584 =
                                                let uu____16586 =
                                                  FStar_Util.right lbname in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____16586 in
                                              if uu____16584
                                              then
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  tm tvar_args
                                                  tm.FStar_Syntax_Syntax.pos
                                              else tm in
                                            FStar_Syntax_InstFV.inst
                                              instantiate_lbname_with_app e1
                                          else e1 in
                                        let t =
                                          let uu____16595 =
                                            let uu____16596 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____16596.FStar_Syntax_Syntax.n in
                                          match uu____16595 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs, cod) ->
                                              let uu____16621 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____16621 with
                                               | (bs1, cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____16632 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____16636 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____16636, gen_tvars)) in
                             (match uu____16445 with
                              | (e1, c1, gvs) ->
                                  (lbname, gen_univs1, e1, c1, gvs)))) in
               FStar_Pervasives_Native.Some ecs)
let (generalize' :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.comp) Prims.list ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_Syntax_Syntax.binder Prims.list) Prims.list)
  =
  fun env ->
    fun is_rec ->
      fun lecs ->
        (let uu____16783 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____16783
         then
           let uu____16786 =
             let uu____16788 =
               FStar_List.map
                 (fun uu____16803 ->
                    match uu____16803 with
                    | (lb, uu____16812, uu____16813) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_All.pipe_right uu____16788 (FStar_String.concat ", ") in
           FStar_Util.print1 "Generalizing: %s\n" uu____16786
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____16839 ->
                match uu____16839 with
                | (l, t, c) -> gather_free_univnames env t) lecs in
         let generalized_lecs =
           let uu____16868 = gen env is_rec lecs in
           match uu____16868 with
           | FStar_Pervasives_Native.None ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____16967 ->
                       match uu____16967 with
                       | (l, t, c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____17029 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 if uu____17029
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____17077 ->
                           match uu____17077 with
                           | (l, us, e, c, gvs) ->
                               let uu____17111 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos in
                               let uu____17113 =
                                 FStar_Syntax_Print.lbname_to_string l in
                               let uu____17115 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c) in
                               let uu____17117 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____17119 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____17111 uu____17113 uu____17115
                                 uu____17117 uu____17119))
                 else ());
                luecs) in
         FStar_List.map2
           (fun univnames ->
              fun uu____17164 ->
                match uu____17164 with
                | (l, generalized_univs, t, c, gvs) ->
                    let uu____17208 =
                      check_universe_generalization univnames
                        generalized_univs t in
                    (l, uu____17208, t, c, gvs)) univnames_lecs
           generalized_lecs)
let (generalize :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.comp) Prims.list ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_Syntax_Syntax.binder Prims.list) Prims.list)
  =
  fun env ->
    fun is_rec ->
      fun lecs ->
        let uu____17263 =
          let uu____17267 =
            let uu____17269 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.string_of_lid uu____17269 in
          FStar_Pervasives_Native.Some uu____17267 in
        FStar_Profiling.profile
          (fun uu____17286 -> generalize' env is_rec lecs) uu____17263
          "FStar.TypeChecker.Util.generalize"
let (check_has_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun e ->
      fun lc ->
        fun t2 ->
          let env1 =
            FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
          let check env2 t1 t21 =
            if env2.FStar_TypeChecker_Env.use_eq_strict
            then
              let uu____17343 =
                FStar_TypeChecker_Rel.get_teq_predicate env2 t1 t21 in
              match uu____17343 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some f ->
                  let uu____17349 = FStar_TypeChecker_Env.apply_guard f e in
                  FStar_All.pipe_right uu____17349
                    (fun uu____17352 ->
                       FStar_Pervasives_Native.Some uu____17352)
            else
              if env2.FStar_TypeChecker_Env.use_eq
              then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
              else
                (let uu____17361 =
                   FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21 in
                 match uu____17361 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some f ->
                     let uu____17367 = FStar_TypeChecker_Env.apply_guard f e in
                     FStar_All.pipe_left
                       (fun uu____17370 ->
                          FStar_Pervasives_Native.Some uu____17370)
                       uu____17367) in
          let uu____17371 = maybe_coerce_lc env1 e lc t2 in
          match uu____17371 with
          | (e1, lc1, g_c) ->
              let uu____17387 =
                check env1 lc1.FStar_TypeChecker_Common.res_typ t2 in
              (match uu____17387 with
               | FStar_Pervasives_Native.None ->
                   let uu____17396 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ in
                   let uu____17402 = FStar_TypeChecker_Env.get_range env1 in
                   FStar_Errors.raise_error uu____17396 uu____17402
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____17411 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____17411
                     then
                       let uu____17416 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____17416
                     else ());
                    (let uu____17422 = FStar_TypeChecker_Env.conj_guard g g_c in
                     (e1, lc1, uu____17422))))
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env ->
    fun g ->
      fun lc ->
        (let uu____17450 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium in
         if uu____17450
         then
           let uu____17453 = FStar_TypeChecker_Common.lcomp_to_string lc in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____17453
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
         let uu____17467 = FStar_TypeChecker_Common.lcomp_comp lc in
         match uu____17467 with
         | (c, g_c) ->
             let uu____17479 = FStar_TypeChecker_Common.is_total_lcomp lc in
             if uu____17479
             then
               let uu____17487 =
                 let uu____17489 = FStar_TypeChecker_Env.conj_guard g1 g_c in
                 discharge uu____17489 in
               (uu____17487, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] in
                let c1 =
                  let uu____17497 =
                    let uu____17498 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    FStar_All.pipe_right uu____17498
                      FStar_Syntax_Syntax.mk_Comp in
                  FStar_All.pipe_right uu____17497
                    (FStar_TypeChecker_Normalize.normalize_comp steps env) in
                let uu____17499 = check_trivial_precondition env c1 in
                match uu____17499 with
                | (ct, vc, g_pre) ->
                    ((let uu____17515 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification") in
                      if uu____17515
                      then
                        let uu____17520 =
                          FStar_Syntax_Print.term_to_string vc in
                        FStar_Util.print1 "top-level VC: %s\n" uu____17520
                      else ());
                     (let uu____17525 =
                        let uu____17527 =
                          let uu____17528 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre in
                          FStar_TypeChecker_Env.conj_guard g1 uu____17528 in
                        discharge uu____17527 in
                      let uu____17529 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp in
                      (uu____17525, uu____17529)))))
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head ->
    fun seen_args ->
      let short_bin_op f uu___8_17563 =
        match uu___8_17563 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst, uu____17573)::[] -> f fst
        | uu____17598 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____17610 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____17610
          (fun uu____17611 -> FStar_TypeChecker_Common.NonTrivial uu____17611) in
      let op_or_e e =
        let uu____17622 =
          let uu____17623 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____17623 in
        FStar_All.pipe_right uu____17622
          (fun uu____17626 -> FStar_TypeChecker_Common.NonTrivial uu____17626) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun uu____17633 -> FStar_TypeChecker_Common.NonTrivial uu____17633) in
      let op_or_t t =
        let uu____17644 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____17644
          (fun uu____17647 -> FStar_TypeChecker_Common.NonTrivial uu____17647) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun uu____17654 -> FStar_TypeChecker_Common.NonTrivial uu____17654) in
      let short_op_ite uu___9_17660 =
        match uu___9_17660 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard, uu____17670)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard, uu____17697)::[] ->
            let uu____17738 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____17738
              (fun uu____17739 ->
                 FStar_TypeChecker_Common.NonTrivial uu____17739)
        | uu____17740 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____17752 =
          let uu____17760 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____17760) in
        let uu____17768 =
          let uu____17778 =
            let uu____17786 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____17786) in
          let uu____17794 =
            let uu____17804 =
              let uu____17812 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____17812) in
            let uu____17820 =
              let uu____17830 =
                let uu____17838 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____17838) in
              let uu____17846 =
                let uu____17856 =
                  let uu____17864 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____17864) in
                [uu____17856; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____17830 :: uu____17846 in
            uu____17804 :: uu____17820 in
          uu____17778 :: uu____17794 in
        uu____17752 :: uu____17768 in
      match head.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____17926 =
            FStar_Util.find_map table
              (fun uu____17941 ->
                 match uu____17941 with
                 | (x, mk) ->
                     let uu____17958 = FStar_Ident.lid_equals x lid in
                     if uu____17958
                     then
                       let uu____17963 = mk seen_args in
                       FStar_Pervasives_Native.Some uu____17963
                     else FStar_Pervasives_Native.None) in
          (match uu____17926 with
           | FStar_Pervasives_Native.None -> FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____17967 -> FStar_TypeChecker_Common.Trivial
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l ->
    let uu____17975 =
      let uu____17976 = FStar_Syntax_Util.un_uinst l in
      uu____17976.FStar_Syntax_Syntax.n in
    match uu____17975 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____17981 -> false
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env ->
    fun bs ->
      let pos bs1 =
        match bs1 with
        | (hd, uu____18017)::uu____18018 ->
            FStar_Syntax_Syntax.range_of_bv hd
        | uu____18037 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____18046, FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____18047))::uu____18048 -> bs
      | uu____18066 ->
          let uu____18067 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____18067 with
           | FStar_Pervasives_Native.None -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____18071 =
                 let uu____18072 = FStar_Syntax_Subst.compress t in
                 uu____18072.FStar_Syntax_Syntax.n in
               (match uu____18071 with
                | FStar_Syntax_Syntax.Tm_arrow (bs', uu____18076) ->
                    let uu____18097 =
                      FStar_Util.prefix_until
                        (fun uu___10_18137 ->
                           match uu___10_18137 with
                           | (uu____18145, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____18146)) ->
                               false
                           | uu____18151 -> true) bs' in
                    (match uu____18097 with
                     | FStar_Pervasives_Native.None -> bs
                     | FStar_Pervasives_Native.Some
                         ([], uu____18187, uu____18188) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps, uu____18260, uu____18261) ->
                         let uu____18334 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____18355 ->
                                   match uu____18355 with
                                   | (x, uu____18364) ->
                                       let uu____18369 =
                                         FStar_Ident.string_of_id
                                           x.FStar_Syntax_Syntax.ppname in
                                       FStar_Util.starts_with uu____18369 "'")) in
                         if uu____18334
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____18415 ->
                                     match uu____18415 with
                                     | (x, i) ->
                                         let uu____18434 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____18434, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____18445 -> bs))
let (maybe_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun e ->
      fun c1 ->
        fun c2 ->
          fun t ->
            let m1 = FStar_TypeChecker_Env.norm_eff_name env c1 in
            let m2 = FStar_TypeChecker_Env.norm_eff_name env c2 in
            let uu____18474 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1)) in
            if uu____18474
            then e
            else
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_meta
                   (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                e.FStar_Syntax_Syntax.pos
let (maybe_monadic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun e ->
      fun c ->
        fun t ->
          let m = FStar_TypeChecker_Env.norm_eff_name env c in
          let uu____18505 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____18505
          then e
          else
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_meta
                 (e, (FStar_Syntax_Syntax.Meta_monadic (m, t))))
              e.FStar_Syntax_Syntax.pos
let (d : Prims.string -> unit) =
  fun s -> FStar_Util.print1 "\027[01;36m%s\027[00m\n" s
let (mk_toplevel_definition :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term))
  =
  fun env ->
    fun lident ->
      fun def ->
        (let uu____18548 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____18548
         then
           ((let uu____18553 = FStar_Ident.string_of_lid lident in
             d uu____18553);
            (let uu____18555 = FStar_Ident.string_of_lid lident in
             let uu____18557 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____18555 uu____18557))
         else ());
        (let fv =
           let uu____18563 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____18563
             FStar_Pervasives_Native.None in
         let lbname = FStar_Util.Inr fv in
         let lb =
           (false,
             [FStar_Syntax_Util.mk_letbinding lbname []
                FStar_Syntax_Syntax.tun FStar_Parser_Const.effect_Tot_lid def
                [] FStar_Range.dummyRange]) in
         let sig_ctx =
           FStar_Syntax_Syntax.mk_sigelt
             (FStar_Syntax_Syntax.Sig_let (lb, [lident])) in
         let uu____18575 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Range.dummyRange in
         ((let uu___2127_18577 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2127_18577.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2127_18577.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2127_18577.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2127_18577.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2127_18577.FStar_Syntax_Syntax.sigopts)
           }), uu____18575))
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env ->
    fun se ->
      let visibility uu___11_18595 =
        match uu___11_18595 with
        | FStar_Syntax_Syntax.Private -> true
        | uu____18598 -> false in
      let reducibility uu___12_18606 =
        match uu___12_18606 with
        | FStar_Syntax_Syntax.Abstract -> true
        | FStar_Syntax_Syntax.Irreducible -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> true
        | FStar_Syntax_Syntax.Visible_default -> true
        | FStar_Syntax_Syntax.Inline_for_extraction -> true
        | uu____18613 -> false in
      let assumption uu___13_18621 =
        match uu___13_18621 with
        | FStar_Syntax_Syntax.Assumption -> true
        | FStar_Syntax_Syntax.New -> true
        | uu____18625 -> false in
      let reification uu___14_18633 =
        match uu___14_18633 with
        | FStar_Syntax_Syntax.Reifiable -> true
        | FStar_Syntax_Syntax.Reflectable uu____18636 -> true
        | uu____18638 -> false in
      let inferred uu___15_18646 =
        match uu___15_18646 with
        | FStar_Syntax_Syntax.Discriminator uu____18648 -> true
        | FStar_Syntax_Syntax.Projector uu____18650 -> true
        | FStar_Syntax_Syntax.RecordType uu____18656 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____18666 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor -> true
        | FStar_Syntax_Syntax.HasMaskedEffect -> true
        | FStar_Syntax_Syntax.Effect -> true
        | uu____18679 -> false in
      let has_eq uu___16_18687 =
        match uu___16_18687 with
        | FStar_Syntax_Syntax.Noeq -> true
        | FStar_Syntax_Syntax.Unopteq -> true
        | uu____18691 -> false in
      let quals_combo_ok quals q =
        match q with
        | FStar_Syntax_Syntax.Assumption ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                          (inferred x))
                         || (visibility x))
                        || (assumption x))
                       ||
                       (env.FStar_TypeChecker_Env.is_iface &&
                          (x = FStar_Syntax_Syntax.Inline_for_extraction)))
                      || (x = FStar_Syntax_Syntax.NoExtract)))
        | FStar_Syntax_Syntax.New ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    (((x = q) || (inferred x)) || (visibility x)) ||
                      (assumption x)))
        | FStar_Syntax_Syntax.Inline_for_extraction ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (visibility x))
                           || (reducibility x))
                          || (reification x))
                         || (inferred x))
                        || (has_eq x))
                       ||
                       (env.FStar_TypeChecker_Env.is_iface &&
                          (x = FStar_Syntax_Syntax.Assumption)))
                      || (x = FStar_Syntax_Syntax.NoExtract)))
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Visible_default ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Irreducible ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Abstract ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Noeq ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Unopteq ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.TotalEffect ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    (((x = q) || (inferred x)) || (visibility x)) ||
                      (reification x)))
        | FStar_Syntax_Syntax.Logic ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    ((((x = q) || (x = FStar_Syntax_Syntax.Assumption)) ||
                        (inferred x))
                       || (visibility x))
                      || (reducibility x)))
        | FStar_Syntax_Syntax.Reifiable ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Reflectable uu____18770 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private -> true
        | uu____18777 -> true in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1 in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l ->
                  let uu____18810 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l in
                  FStar_Option.isSome uu____18810)) in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____18841 = FStar_Option.get attrs_opt in
                     FStar_Syntax_Util.has_attribute uu____18841
                       FStar_Parser_Const.erasable_attr))) in
        let se_has_erasable_attr =
          FStar_Syntax_Util.has_attribute se1.FStar_Syntax_Syntax.sigattrs
            FStar_Parser_Const.erasable_attr in
        if
          (val_exists && val_has_erasable_attr) &&
            (Prims.op_Negation se_has_erasable_attr)
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_QulifierListNotPermitted,
              "Mismatch of attributes between declaration and definition: Declaration is marked `erasable` but the definition is not")
            r
        else ();
        if
          (val_exists && (Prims.op_Negation val_has_erasable_attr)) &&
            se_has_erasable_attr
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_QulifierListNotPermitted,
              "Mismatch of attributed between declaration and definition: Definition is marked `erasable` but the declaration is not")
            r
        else ();
        if se_has_erasable_attr
        then
          (match se1.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_bundle uu____18861 ->
               let uu____18870 =
                 let uu____18872 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_18878 ->
                           match uu___17_18878 with
                           | FStar_Syntax_Syntax.Noeq -> true
                           | uu____18881 -> false)) in
                 Prims.op_Negation uu____18872 in
               if uu____18870
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____18888 -> ()
           | FStar_Syntax_Syntax.Sig_fail uu____18895 -> ()
           | uu____18908 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_QulifierListNotPermitted,
                   "Illegal attribute: the `erasable` attribute is only permitted on inductive type definitions")
                 r)
        else () in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic))) in
      let uu____18922 =
        let uu____18924 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_18930 ->
                  match uu___18_18930 with
                  | FStar_Syntax_Syntax.OnlyName -> true
                  | uu____18933 -> false)) in
        FStar_All.pipe_right uu____18924 Prims.op_Negation in
      if uu____18922
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x -> fun y -> x = y) quals in
        let err' msg =
          let uu____18954 =
            let uu____18960 =
              let uu____18962 = FStar_Syntax_Print.quals_to_string quals in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____18962 msg in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____18960) in
          FStar_Errors.raise_error uu____18954 r in
        let err msg = err' (Prims.op_Hat ": " msg) in
        let err'1 uu____18980 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____18988 =
            let uu____18990 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____18990 in
          if uu____18988 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec, uu____19001), uu____19002)
              ->
              ((let uu____19014 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____19014
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____19023 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x -> (assumption x) || (has_eq x))) in
                if uu____19023
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____19034 ->
              ((let uu____19044 =
                  let uu____19046 =
                    FStar_All.pipe_right quals
                      (FStar_Util.for_all
                         (fun x ->
                            (((((x = FStar_Syntax_Syntax.Abstract) ||
                                  (x =
                                     FStar_Syntax_Syntax.Inline_for_extraction))
                                 || (x = FStar_Syntax_Syntax.NoExtract))
                                || (inferred x))
                               || (visibility x))
                              || (has_eq x))) in
                  Prims.op_Negation uu____19046 in
                if uu____19044 then err'1 () else ());
               (let uu____19056 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_19062 ->
                           match uu___19_19062 with
                           | FStar_Syntax_Syntax.Unopteq -> true
                           | uu____19065 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr) in
                if uu____19056
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____19071 ->
              let uu____19078 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____19078 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____19086 ->
              let uu____19093 =
                let uu____19095 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____19095 in
              if uu____19093 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____19105 ->
              let uu____19106 =
                let uu____19108 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____19108 in
              if uu____19106 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19118 ->
              let uu____19131 =
                let uu____19133 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____19133 in
              if uu____19131 then err'1 () else ()
          | uu____19143 -> ()))
      else ()
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g ->
    fun t ->
      let rec descend env t1 =
        let uu____19182 =
          let uu____19183 = FStar_Syntax_Subst.compress t1 in
          uu____19183.FStar_Syntax_Syntax.n in
        match uu____19182 with
        | FStar_Syntax_Syntax.Tm_arrow uu____19187 ->
            let uu____19202 = FStar_Syntax_Util.arrow_formals_comp t1 in
            (match uu____19202 with
             | (bs, c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____19211;
               FStar_Syntax_Syntax.index = uu____19212;
               FStar_Syntax_Syntax.sort = t2;_},
             uu____19214)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head, uu____19223) -> descend env head
        | FStar_Syntax_Syntax.Tm_uinst (head, uu____19249) ->
            descend env head
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____19255 -> false
      and aux env t1 =
        let t2 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Primops;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF;
            FStar_TypeChecker_Env.UnfoldUntil
              FStar_Syntax_Syntax.delta_constant;
            FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.AllowUnboundUniverses;
            FStar_TypeChecker_Env.Zeta;
            FStar_TypeChecker_Env.Iota;
            FStar_TypeChecker_Env.Unascribe] env t1 in
        let res =
          (FStar_TypeChecker_Env.non_informative env t2) || (descend env t2) in
        (let uu____19265 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction") in
         if uu____19265
         then
           let uu____19270 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____19270
         else ());
        res in
      aux g t
let (fresh_effect_repr :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.tscheme ->
          FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option ->
            FStar_Syntax_Syntax.universe ->
              FStar_Syntax_Syntax.term ->
                (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun r ->
      fun eff_name ->
        fun signature_ts ->
          fun repr_ts_opt ->
            fun u ->
              fun a_tm ->
                let fail t =
                  let uu____19335 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t in
                  FStar_Errors.raise_error uu____19335 r in
                let uu____19345 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts in
                match uu____19345 with
                | (uu____19354, signature) ->
                    let uu____19356 =
                      let uu____19357 = FStar_Syntax_Subst.compress signature in
                      uu____19357.FStar_Syntax_Syntax.n in
                    (match uu____19356 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs, uu____19365) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____19413 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b ->
                                     let uu____19429 =
                                       FStar_Syntax_Print.binder_to_string b in
                                     let uu____19431 =
                                       FStar_Ident.string_of_lid eff_name in
                                     let uu____19433 =
                                       FStar_Range.string_of_range r in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____19429 uu____19431 uu____19433) r in
                              (match uu____19413 with
                               | (is, g) ->
                                   let uu____19446 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None ->
                                         let eff_c =
                                           let uu____19448 =
                                             let uu____19449 =
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 is in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = [u];
                                               FStar_Syntax_Syntax.effect_name
                                                 = eff_name;
                                               FStar_Syntax_Syntax.result_typ
                                                 = a_tm;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____19449;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____19448 in
                                         let uu____19468 =
                                           let uu____19469 =
                                             let uu____19484 =
                                               let uu____19493 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   FStar_Syntax_Syntax.t_unit in
                                               [uu____19493] in
                                             (uu____19484, eff_c) in
                                           FStar_Syntax_Syntax.Tm_arrow
                                             uu____19469 in
                                         FStar_Syntax_Syntax.mk uu____19468 r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____19524 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u] in
                                           FStar_All.pipe_right uu____19524
                                             FStar_Pervasives_Native.snd in
                                         let uu____19533 =
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg (a_tm
                                             :: is) in
                                         FStar_Syntax_Syntax.mk_Tm_app repr
                                           uu____19533 r in
                                   (uu____19446, g))
                          | uu____19542 -> fail signature)
                     | uu____19543 -> fail signature)
let (fresh_effect_repr_en :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.universe ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun r ->
      fun eff_name ->
        fun u ->
          fun a_tm ->
            let uu____19574 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env) in
            FStar_All.pipe_right uu____19574
              (fun ed ->
                 let uu____19582 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____19582 u a_tm)
let (layered_effect_indices_as_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.tscheme ->
          FStar_Syntax_Syntax.universe ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binders)
  =
  fun env ->
    fun r ->
      fun eff_name ->
        fun sig_ts ->
          fun u ->
            fun a_tm ->
              let uu____19618 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u] in
              match uu____19618 with
              | (uu____19623, sig_tm) ->
                  let fail t =
                    let uu____19631 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t in
                    FStar_Errors.raise_error uu____19631 r in
                  let uu____19637 =
                    let uu____19638 = FStar_Syntax_Subst.compress sig_tm in
                    uu____19638.FStar_Syntax_Syntax.n in
                  (match uu____19637 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs, uu____19642) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs in
                       (match bs1 with
                        | (a', uu____19665)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____19687 -> fail sig_tm)
                   | uu____19688 -> fail sig_tm)
let (lift_tf_layered_effect :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun tgt ->
    fun lift_ts ->
      fun env ->
        fun c ->
          (let uu____19719 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects") in
           if uu____19719
           then
             let uu____19724 = FStar_Syntax_Print.comp_to_string c in
             let uu____19726 = FStar_Syntax_Print.lid_to_string tgt in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____19724 uu____19726
           else ());
          (let r = FStar_TypeChecker_Env.get_range env in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c in
           let lift_name =
             let uu____19735 =
               FStar_Ident.string_of_lid ct.FStar_Syntax_Syntax.effect_name in
             let uu____19737 = FStar_Ident.string_of_lid tgt in
             FStar_Util.format2 "%s ~> %s" uu____19735 uu____19737 in
           let uu____19740 =
             let uu____19751 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs in
             let uu____19752 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst) in
             (uu____19751, (ct.FStar_Syntax_Syntax.result_typ), uu____19752) in
           match uu____19740 with
           | (u, a, c_is) ->
               let uu____19800 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u] in
               (match uu____19800 with
                | (uu____19809, lift_t) ->
                    let lift_t_shape_error s =
                      let uu____19820 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name in
                      let uu____19822 = FStar_Ident.string_of_lid tgt in
                      let uu____19824 =
                        FStar_Syntax_Print.term_to_string lift_t in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____19820 uu____19822 s uu____19824 in
                    let uu____19827 =
                      let uu____19860 =
                        let uu____19861 = FStar_Syntax_Subst.compress lift_t in
                        uu____19861.FStar_Syntax_Syntax.n in
                      match uu____19860 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs, c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____19925 =
                            FStar_Syntax_Subst.open_comp bs c1 in
                          (match uu____19925 with
                           | (a_b::bs1, c2) ->
                               let uu____19985 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one)) in
                               (a_b, uu____19985, c2))
                      | uu____20073 ->
                          let uu____20074 =
                            let uu____20080 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders" in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____20080) in
                          FStar_Errors.raise_error uu____20074 r in
                    (match uu____19827 with
                     | (a_b, (rest_bs, f_b::[]), lift_c) ->
                         let uu____20198 =
                           let uu____20205 =
                             let uu____20206 =
                               let uu____20207 =
                                 let uu____20214 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst in
                                 (uu____20214, a) in
                               FStar_Syntax_Syntax.NT uu____20207 in
                             [uu____20206] in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____20205
                             (fun b ->
                                let uu____20231 =
                                  FStar_Syntax_Print.binder_to_string b in
                                let uu____20233 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name in
                                let uu____20235 =
                                  FStar_Ident.string_of_lid tgt in
                                let uu____20237 =
                                  FStar_Range.string_of_range r in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____20231 uu____20233 uu____20235
                                  uu____20237) r in
                         (match uu____20198 with
                          | (rest_bs_uvars, g) ->
                              ((let uu____20251 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects") in
                                if uu____20251
                                then
                                  let uu____20256 =
                                    FStar_List.fold_left
                                      (fun s ->
                                         fun u1 ->
                                           let uu____20265 =
                                             let uu____20267 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1 in
                                             Prims.op_Hat ";;;;" uu____20267 in
                                           Prims.op_Hat s uu____20265) ""
                                      rest_bs_uvars in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____20256
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b ->
                                       fun t ->
                                         let uu____20298 =
                                           let uu____20305 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst in
                                           (uu____20305, t) in
                                         FStar_Syntax_Syntax.NT uu____20298)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars) in
                                let guard_f =
                                  let f_sort =
                                    let uu____20324 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs) in
                                    FStar_All.pipe_right uu____20324
                                      FStar_Syntax_Subst.compress in
                                  let f_sort_is =
                                    let uu____20330 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name in
                                    effect_args_from_repr f_sort uu____20330
                                      r in
                                  FStar_List.fold_left2
                                    (fun g1 ->
                                       fun i1 ->
                                         fun i2 ->
                                           let uu____20339 =
                                             FStar_TypeChecker_Rel.layered_effect_teq
                                               env i1 i2
                                               (FStar_Pervasives_Native.Some
                                                  lift_name) in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____20339)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is in
                                let lift_ct =
                                  let uu____20342 =
                                    FStar_All.pipe_right lift_c
                                      (FStar_Syntax_Subst.subst_comp substs) in
                                  FStar_All.pipe_right uu____20342
                                    FStar_Syntax_Util.comp_to_comp_typ in
                                let is =
                                  let uu____20346 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____20346 r in
                                let fml =
                                  let uu____20351 =
                                    let uu____20356 =
                                      FStar_List.hd
                                        lift_ct.FStar_Syntax_Syntax.comp_univs in
                                    let uu____20357 =
                                      let uu____20358 =
                                        FStar_List.hd
                                          lift_ct.FStar_Syntax_Syntax.effect_args in
                                      FStar_Pervasives_Native.fst uu____20358 in
                                    (uu____20356, uu____20357) in
                                  match uu____20351 with
                                  | (u1, wp) ->
                                      FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                        env u1
                                        lift_ct.FStar_Syntax_Syntax.result_typ
                                        wp FStar_Range.dummyRange in
                                (let uu____20384 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects"))
                                     &&
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme) in
                                 if uu____20384
                                 then
                                   let uu____20390 =
                                     FStar_Syntax_Print.term_to_string fml in
                                   FStar_Util.print1 "Guard for lift is: %s"
                                     uu____20390
                                 else ());
                                (let c1 =
                                   let uu____20396 =
                                     let uu____20397 =
                                       FStar_All.pipe_right is
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.as_arg) in
                                     {
                                       FStar_Syntax_Syntax.comp_univs =
                                         (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                       FStar_Syntax_Syntax.effect_name = tgt;
                                       FStar_Syntax_Syntax.result_typ = a;
                                       FStar_Syntax_Syntax.effect_args =
                                         uu____20397;
                                       FStar_Syntax_Syntax.flags = []
                                     } in
                                   FStar_Syntax_Syntax.mk_Comp uu____20396 in
                                 (let uu____20421 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects") in
                                  if uu____20421
                                  then
                                    let uu____20426 =
                                      FStar_Syntax_Print.comp_to_string c1 in
                                    FStar_Util.print1 "} Lifted comp: %s\n"
                                      uu____20426
                                  else ());
                                 (let uu____20431 =
                                    let uu____20432 =
                                      FStar_TypeChecker_Env.conj_guard g
                                        guard_f in
                                    let uu____20433 =
                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                        (FStar_TypeChecker_Common.NonTrivial
                                           fml) in
                                    FStar_TypeChecker_Env.conj_guard
                                      uu____20432 uu____20433 in
                                  (c1, uu____20431)))))))))
let lift_tf_layered_effect_term :
  'uuuuuu20447 .
    'uuuuuu20447 ->
      FStar_Syntax_Syntax.sub_eff ->
        FStar_Syntax_Syntax.universe ->
          FStar_Syntax_Syntax.typ ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env ->
    fun sub ->
      fun u ->
        fun a ->
          fun e ->
            let lift =
              let uu____20476 =
                let uu____20481 =
                  FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift
                    FStar_Util.must in
                FStar_All.pipe_right uu____20481
                  (fun ts -> FStar_TypeChecker_Env.inst_tscheme_with ts [u]) in
              FStar_All.pipe_right uu____20476 FStar_Pervasives_Native.snd in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must in
              let uu____20524 =
                let uu____20525 =
                  let uu____20528 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd in
                  FStar_All.pipe_right uu____20528
                    FStar_Syntax_Subst.compress in
                uu____20525.FStar_Syntax_Syntax.n in
              match uu____20524 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____20551::bs, uu____20553)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____20593 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one)) in
                  FStar_All.pipe_right uu____20593
                    FStar_Pervasives_Native.fst
              | uu____20699 ->
                  let uu____20700 =
                    let uu____20706 =
                      let uu____20708 =
                        FStar_Syntax_Print.tscheme_to_string lift_t in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____20708 in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____20706) in
                  FStar_Errors.raise_error uu____20700
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos in
            let args =
              let uu____20735 = FStar_Syntax_Syntax.as_arg a in
              let uu____20744 =
                let uu____20755 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____20791 ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const)) in
                let uu____20798 =
                  let uu____20809 = FStar_Syntax_Syntax.as_arg e in
                  [uu____20809] in
                FStar_List.append uu____20755 uu____20798 in
              uu____20735 :: uu____20744 in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              e.FStar_Syntax_Syntax.pos
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env ->
    fun datacon ->
      fun index ->
        let uu____20880 = FStar_TypeChecker_Env.lookup_datacon env datacon in
        match uu____20880 with
        | (uu____20885, t) ->
            let err n =
              let uu____20895 =
                let uu____20901 =
                  let uu____20903 = FStar_Ident.string_of_lid datacon in
                  let uu____20905 = FStar_Util.string_of_int n in
                  let uu____20907 = FStar_Util.string_of_int index in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____20903 uu____20905 uu____20907 in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____20901) in
              let uu____20911 = FStar_TypeChecker_Env.get_range env in
              FStar_Errors.raise_error uu____20895 uu____20911 in
            let uu____20912 =
              let uu____20913 = FStar_Syntax_Subst.compress t in
              uu____20913.FStar_Syntax_Syntax.n in
            (match uu____20912 with
             | FStar_Syntax_Syntax.Tm_arrow (bs, uu____20917) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____20972 ->
                           match uu____20972 with
                           | (uu____20980, q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true)) ->
                                    false
                                | uu____20989 -> true))) in
                 if (FStar_List.length bs1) <= index
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index in
                    FStar_Syntax_Util.mk_field_projector_name datacon
                      (FStar_Pervasives_Native.fst b) index)
             | uu____21023 -> err Prims.int_zero)
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env ->
    fun sub ->
      let uu____21036 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub.FStar_Syntax_Syntax.target) in
      if uu____21036
      then
        let uu____21039 =
          let uu____21052 =
            FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must in
          lift_tf_layered_effect sub.FStar_Syntax_Syntax.target uu____21052 in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____21039;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c in
           let uu____21087 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs in
           match uu____21087 with
           | (uu____21096, lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args in
               let uu____21115 =
                 let uu____21116 =
                   let uu___2504_21117 = ct in
                   let uu____21118 =
                     let uu____21129 =
                       let uu____21138 =
                         let uu____21139 =
                           let uu____21140 =
                             let uu____21157 =
                               let uu____21168 =
                                 FStar_Syntax_Syntax.as_arg
                                   ct.FStar_Syntax_Syntax.result_typ in
                               [uu____21168; wp] in
                             (lift_t, uu____21157) in
                           FStar_Syntax_Syntax.Tm_app uu____21140 in
                         FStar_Syntax_Syntax.mk uu____21139
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos in
                       FStar_All.pipe_right uu____21138
                         FStar_Syntax_Syntax.as_arg in
                     [uu____21129] in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2504_21117.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2504_21117.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____21118;
                     FStar_Syntax_Syntax.flags =
                       (uu___2504_21117.FStar_Syntax_Syntax.flags)
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____21116 in
               (uu____21115, FStar_TypeChecker_Common.trivial_guard) in
         let mk_mlift_term ts u r e =
           let uu____21268 = FStar_TypeChecker_Env.inst_tscheme_with ts [u] in
           match uu____21268 with
           | (uu____21275, lift_t) ->
               let uu____21277 =
                 let uu____21278 =
                   let uu____21295 =
                     let uu____21306 = FStar_Syntax_Syntax.as_arg r in
                     let uu____21315 =
                       let uu____21326 =
                         FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun in
                       let uu____21335 =
                         let uu____21346 = FStar_Syntax_Syntax.as_arg e in
                         [uu____21346] in
                       uu____21326 :: uu____21335 in
                     uu____21306 :: uu____21315 in
                   (lift_t, uu____21295) in
                 FStar_Syntax_Syntax.Tm_app uu____21278 in
               FStar_Syntax_Syntax.mk uu____21277 e.FStar_Syntax_Syntax.pos in
         let uu____21399 =
           let uu____21412 =
             FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must in
           FStar_All.pipe_right uu____21412 mk_mlift_wp in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____21399;
           FStar_TypeChecker_Env.mlift_term =
             (match sub.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____21448 ->
                        fun uu____21449 -> fun e -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env ->
    fun sub ->
      let uu____21472 = get_mlift_for_subeff env sub in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub.FStar_Syntax_Syntax.source sub.FStar_Syntax_Syntax.target
        uu____21472
let (update_env_polymonadic_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.tscheme -> FStar_TypeChecker_Env.env)
  =
  fun env ->
    fun m ->
      fun n ->
        fun p ->
          fun ty ->
            FStar_TypeChecker_Env.add_polymonadic_bind env m n p
              (fun env1 ->
                 fun c1 ->
                   fun bv_opt ->
                     fun c2 ->
                       fun flags ->
                         fun r ->
                           mk_indexed_bind env1 m n p ty c1 bv_opt c2 flags r)