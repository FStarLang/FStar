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
let (maybe_assume_result_eq_pure_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env ->
    fun e ->
      fun lc ->
        let should_return1 =
          (((Prims.op_Negation env.FStar_TypeChecker_Env.lax) &&
              (FStar_TypeChecker_Env.lid_exists env
                 FStar_Parser_Const.effect_GTot_lid))
             && (should_return env (FStar_Pervasives_Native.Some e) lc))
            &&
            (let uu____7064 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc in
             Prims.op_Negation uu____7064) in
        let flags =
          if should_return1
          then
            let uu____7072 = FStar_TypeChecker_Common.is_total_lcomp lc in
            (if uu____7072
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags in
        let refine uu____7092 =
          let uu____7093 = FStar_TypeChecker_Common.lcomp_comp lc in
          match uu____7093 with
          | (c, g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c) in
              let uu____7108 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
              if uu____7108
              then
                let uu____7117 =
                  return_value env FStar_Parser_Const.effect_PURE_lid
                    (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e in
                (match uu____7117 with
                 | (retc, g_retc) ->
                     let g_c1 = FStar_TypeChecker_Env.conj_guard g_c g_retc in
                     let uu____7131 =
                       let uu____7133 = FStar_Syntax_Util.is_pure_comp c in
                       Prims.op_Negation uu____7133 in
                     if uu____7131
                     then
                       let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                       let retc2 =
                         let uu___906_7144 = retc1 in
                         {
                           FStar_Syntax_Syntax.comp_univs =
                             (uu___906_7144.FStar_Syntax_Syntax.comp_univs);
                           FStar_Syntax_Syntax.effect_name =
                             FStar_Parser_Const.effect_GHOST_lid;
                           FStar_Syntax_Syntax.result_typ =
                             (uu___906_7144.FStar_Syntax_Syntax.result_typ);
                           FStar_Syntax_Syntax.effect_args =
                             (uu___906_7144.FStar_Syntax_Syntax.effect_args);
                           FStar_Syntax_Syntax.flags = flags
                         } in
                       let uu____7145 = FStar_Syntax_Syntax.mk_Comp retc2 in
                       (uu____7145, g_c1)
                     else
                       (let uu____7152 =
                          FStar_Syntax_Util.comp_set_flags retc flags in
                        (uu____7152, g_c1)))
              else
                (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 let t = c1.FStar_Syntax_Syntax.result_typ in
                 let c2 = FStar_Syntax_Syntax.mk_Comp c1 in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (t.FStar_Syntax_Syntax.pos)) t in
                 let xexp = FStar_Syntax_Syntax.bv_to_name x in
                 let uu____7166 =
                   let uu____7171 =
                     FStar_All.pipe_right c2
                       FStar_Syntax_Util.comp_effect_name in
                   return_value env uu____7171
                     (FStar_Pervasives_Native.Some u_t) t xexp in
                 match uu____7166 with
                 | (ret, g_ret) ->
                     let ret1 =
                       let uu____7183 =
                         FStar_Syntax_Util.comp_set_flags ret
                           [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____7183 in
                     let eq = FStar_Syntax_Util.mk_eq2 u_t t xexp e in
                     let eq_ret =
                       weaken_precondition env ret1
                         (FStar_TypeChecker_Common.NonTrivial eq) in
                     let uu____7186 =
                       let uu____7191 =
                         let uu____7192 =
                           FStar_TypeChecker_Common.lcomp_of_comp c2 in
                         bind e.FStar_Syntax_Syntax.pos env
                           FStar_Pervasives_Native.None uu____7192
                           ((FStar_Pervasives_Native.Some x), eq_ret) in
                       FStar_TypeChecker_Common.lcomp_comp uu____7191 in
                     (match uu____7186 with
                      | (bind_c, g_bind) ->
                          let uu____7203 =
                            FStar_Syntax_Util.comp_set_flags bind_c flags in
                          let uu____7206 =
                            FStar_TypeChecker_Env.conj_guards
                              [g_c; g_ret; g_bind] in
                          (uu____7203, uu____7206))) in
        if Prims.op_Negation should_return1
        then lc
        else
          FStar_TypeChecker_Common.mk_lcomp
            lc.FStar_TypeChecker_Common.eff_name
            lc.FStar_TypeChecker_Common.res_typ flags refine
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
            fun uu____7244 ->
              match uu____7244 with
              | (x, lc2) ->
                  let lc21 =
                    let eff1 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc1.FStar_TypeChecker_Common.eff_name in
                    let eff2 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc2.FStar_TypeChecker_Common.eff_name in
                    let uu____7256 =
                      ((let uu____7260 = is_pure_or_ghost_effect env eff1 in
                        Prims.op_Negation uu____7260) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2) in
                    if uu____7256
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2 in
                  bind r env e1opt lc1 (x, lc21)
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun lid ->
      let uu____7278 =
        let uu____7279 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____7279 in
      FStar_Syntax_Syntax.fvar uu____7278 FStar_Syntax_Syntax.delta_constant
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
                    let uu____7331 =
                      FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                    FStar_Util.format1 "%s.conjunction" uu____7331 in
                  let uu____7334 =
                    let uu____7339 =
                      let uu____7340 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator in
                      FStar_All.pipe_right uu____7340 FStar_Util.must in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7339 [u_a] in
                  match uu____7334 with
                  | (uu____7351, conjunction) ->
                      let uu____7353 =
                        let uu____7362 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args in
                        let uu____7377 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args in
                        (uu____7362, uu____7377) in
                      (match uu____7353 with
                       | (is1, is2) ->
                           let conjunction_t_error s =
                             let uu____7423 =
                               let uu____7425 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction in
                               FStar_Util.format3
                                 "conjunction %s (%s) does not have proper shape (reason:%s)"
                                 uu____7425 conjunction_name s in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7423) in
                           let uu____7429 =
                             let uu____7474 =
                               let uu____7475 =
                                 FStar_Syntax_Subst.compress conjunction in
                               uu____7475.FStar_Syntax_Syntax.n in
                             match uu____7474 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs, body, uu____7524) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____7556 =
                                   FStar_Syntax_Subst.open_term bs body in
                                 (match uu____7556 with
                                  | (a_b::bs1, body1) ->
                                      let uu____7628 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1 in
                                      (match uu____7628 with
                                       | (rest_bs, f_b::g_b::p_b::[]) ->
                                           let uu____7776 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____7776)))
                             | uu____7809 ->
                                 let uu____7810 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders" in
                                 FStar_Errors.raise_error uu____7810 r in
                           (match uu____7429 with
                            | (a_b, rest_bs, f_b, g_b, p_b, body) ->
                                let uu____7935 =
                                  let uu____7942 =
                                    let uu____7943 =
                                      let uu____7944 =
                                        let uu____7951 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst in
                                        (uu____7951, a) in
                                      FStar_Syntax_Syntax.NT uu____7944 in
                                    [uu____7943] in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____7942
                                    (fun b ->
                                       let uu____7967 =
                                         FStar_Syntax_Print.binder_to_string
                                           b in
                                       let uu____7969 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname in
                                       let uu____7971 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____7967 uu____7969 uu____7971) r in
                                (match uu____7935 with
                                 | (rest_bs_uvars, g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b ->
                                            fun t ->
                                              let uu____8009 =
                                                let uu____8016 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst in
                                                (uu____8016, t) in
                                              FStar_Syntax_Syntax.NT
                                                uu____8009) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p])) in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____8055 =
                                           let uu____8056 =
                                             let uu____8059 =
                                               let uu____8060 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst in
                                               uu____8060.FStar_Syntax_Syntax.sort in
                                             FStar_Syntax_Subst.compress
                                               uu____8059 in
                                           uu____8056.FStar_Syntax_Syntax.n in
                                         match uu____8055 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8071, uu____8072::is) ->
                                             let uu____8114 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst) in
                                             FStar_All.pipe_right uu____8114
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8147 ->
                                             let uu____8148 =
                                               conjunction_t_error
                                                 "f's type is not a repr type" in
                                             FStar_Errors.raise_error
                                               uu____8148 r in
                                       FStar_List.fold_left2
                                         (fun g ->
                                            fun i1 ->
                                              fun f_i ->
                                                let uu____8164 =
                                                  FStar_TypeChecker_Rel.layered_effect_teq
                                                    env i1 f_i
                                                    (FStar_Pervasives_Native.Some
                                                       conjunction_name) in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8164)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____8170 =
                                           let uu____8171 =
                                             let uu____8174 =
                                               let uu____8175 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst in
                                               uu____8175.FStar_Syntax_Syntax.sort in
                                             FStar_Syntax_Subst.compress
                                               uu____8174 in
                                           uu____8171.FStar_Syntax_Syntax.n in
                                         match uu____8170 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8186, uu____8187::is) ->
                                             let uu____8229 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst) in
                                             FStar_All.pipe_right uu____8229
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8262 ->
                                             let uu____8263 =
                                               conjunction_t_error
                                                 "g's type is not a repr type" in
                                             FStar_Errors.raise_error
                                               uu____8263 r in
                                       FStar_List.fold_left2
                                         (fun g ->
                                            fun i2 ->
                                              fun g_i ->
                                                let uu____8279 =
                                                  FStar_TypeChecker_Rel.layered_effect_teq
                                                    env i2 g_i
                                                    (FStar_Pervasives_Native.Some
                                                       conjunction_name) in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8279)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body in
                                     let is =
                                       let uu____8285 =
                                         let uu____8286 =
                                           FStar_Syntax_Subst.compress body1 in
                                         uu____8286.FStar_Syntax_Syntax.n in
                                       match uu____8285 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8291, a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8346 ->
                                           let uu____8347 =
                                             conjunction_t_error
                                               "body is not a repr type" in
                                           FStar_Errors.raise_error
                                             uu____8347 r in
                                     let uu____8356 =
                                       let uu____8357 =
                                         let uu____8358 =
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
                                             uu____8358;
                                           FStar_Syntax_Syntax.flags = []
                                         } in
                                       FStar_Syntax_Syntax.mk_Comp uu____8357 in
                                     let uu____8381 =
                                       let uu____8382 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8382 g_guard in
                                     (uu____8356, uu____8381))))
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
                fun uu____8427 ->
                  let if_then_else =
                    let uu____8433 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator in
                    FStar_All.pipe_right uu____8433 FStar_Util.must in
                  let uu____8440 = destruct_wp_comp ct1 in
                  match uu____8440 with
                  | (uu____8451, uu____8452, wp_t) ->
                      let uu____8454 = destruct_wp_comp ct2 in
                      (match uu____8454 with
                       | (uu____8465, uu____8466, wp_e) ->
                           let wp =
                             let uu____8469 =
                               FStar_TypeChecker_Env.inst_effect_fun_with
                                 [u_a] env ed if_then_else in
                             let uu____8470 =
                               let uu____8471 = FStar_Syntax_Syntax.as_arg a in
                               let uu____8480 =
                                 let uu____8491 =
                                   FStar_Syntax_Syntax.as_arg p in
                                 let uu____8500 =
                                   let uu____8511 =
                                     FStar_Syntax_Syntax.as_arg wp_t in
                                   let uu____8520 =
                                     let uu____8531 =
                                       FStar_Syntax_Syntax.as_arg wp_e in
                                     [uu____8531] in
                                   uu____8511 :: uu____8520 in
                                 uu____8491 :: uu____8500 in
                               uu____8471 :: uu____8480 in
                             let uu____8580 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Syntax.mk_Tm_app uu____8469
                               uu____8470 uu____8580 in
                           let uu____8581 = mk_comp ed u_a a wp [] in
                           (uu____8581, FStar_TypeChecker_Env.trivial_guard))
let (comp_pure_wp_false :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun u ->
      fun t ->
        let post_k =
          let uu____8601 =
            let uu____8610 = FStar_Syntax_Syntax.null_binder t in
            [uu____8610] in
          let uu____8629 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
          FStar_Syntax_Util.arrow uu____8601 uu____8629 in
        let kwp =
          let uu____8635 =
            let uu____8644 = FStar_Syntax_Syntax.null_binder post_k in
            [uu____8644] in
          let uu____8663 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
          FStar_Syntax_Util.arrow uu____8635 uu____8663 in
        let post =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k in
        let wp =
          let uu____8670 =
            let uu____8671 = FStar_Syntax_Syntax.mk_binder post in
            [uu____8671] in
          let uu____8690 = fvar_const env FStar_Parser_Const.false_lid in
          FStar_Syntax_Util.abs uu____8670 uu____8690
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
            let uu____8749 =
              let uu____8750 =
                FStar_All.pipe_right scrutinee FStar_Syntax_Syntax.mk_binder in
              [uu____8750] in
            FStar_TypeChecker_Env.push_binders env0 uu____8749 in
          let eff =
            FStar_List.fold_left
              (fun eff ->
                 fun uu____8797 ->
                   match uu____8797 with
                   | (uu____8811, eff_label, uu____8813, uu____8814) ->
                       join_effects env eff eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases in
          let uu____8827 =
            let uu____8835 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu____8873 ->
                      match uu____8873 with
                      | (uu____8888, uu____8889, flags, uu____8891) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___5_8908 ->
                                  match uu___5_8908 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE ->
                                      true
                                  | uu____8911 -> false)))) in
            if uu____8835
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, []) in
          match uu____8827 with
          | (should_not_inline_whole_match, bind_cases_flags) ->
              let bind_cases uu____8948 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
                let uu____8950 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
                if uu____8950
                then
                  let uu____8957 = lax_mk_tot_or_comp_l eff u_res_t res_t [] in
                  (uu____8957, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let maybe_return eff_label_then cthen =
                     let uu____8978 =
                       should_not_inline_whole_match ||
                         (let uu____8981 = is_pure_or_ghost_effect env eff in
                          Prims.op_Negation uu____8981) in
                     if uu____8978 then cthen true else cthen false in
                   let uu____8988 =
                     let uu____8999 =
                       let uu____9012 =
                         let uu____9017 =
                           let uu____9028 =
                             FStar_All.pipe_right lcases
                               (FStar_List.map
                                  (fun uu____9078 ->
                                     match uu____9078 with
                                     | (g, uu____9097, uu____9098,
                                        uu____9099) -> g)) in
                           FStar_All.pipe_right uu____9028
                             (FStar_List.fold_left
                                (fun uu____9147 ->
                                   fun g ->
                                     match uu____9147 with
                                     | (conds, acc) ->
                                         let cond =
                                           let uu____9188 =
                                             FStar_Syntax_Util.mk_neg g in
                                           FStar_Syntax_Util.mk_conj acc
                                             uu____9188 in
                                         ((FStar_List.append conds [cond]),
                                           cond))
                                ([FStar_Syntax_Util.t_true],
                                  FStar_Syntax_Util.t_true)) in
                         FStar_All.pipe_right uu____9017
                           FStar_Pervasives_Native.fst in
                       FStar_All.pipe_right uu____9012
                         (fun l ->
                            FStar_List.splitAt
                              ((FStar_List.length l) - Prims.int_one) l) in
                     FStar_All.pipe_right uu____8999
                       (fun uu____9286 ->
                          match uu____9286 with
                          | (l1, l2) ->
                              let uu____9327 = FStar_List.hd l2 in
                              (l1, uu____9327)) in
                   match uu____8988 with
                   | (neg_branch_conds, exhaustiveness_branch_cond) ->
                       let uu____9356 =
                         match lcases with
                         | [] ->
                             let uu____9387 =
                               comp_pure_wp_false env u_res_t res_t in
                             (FStar_Pervasives_Native.None, uu____9387,
                               FStar_TypeChecker_Env.trivial_guard)
                         | uu____9390 ->
                             let uu____9407 =
                               let uu____9440 =
                                 let uu____9451 =
                                   FStar_All.pipe_right neg_branch_conds
                                     (FStar_List.splitAt
                                        ((FStar_List.length lcases) -
                                           Prims.int_one)) in
                                 FStar_All.pipe_right uu____9451
                                   (fun uu____9523 ->
                                      match uu____9523 with
                                      | (l1, l2) ->
                                          let uu____9564 = FStar_List.hd l2 in
                                          (l1, uu____9564)) in
                               match uu____9440 with
                               | (neg_branch_conds1, neg_last) ->
                                   let uu____9621 =
                                     let uu____9660 =
                                       FStar_All.pipe_right lcases
                                         (FStar_List.splitAt
                                            ((FStar_List.length lcases) -
                                               Prims.int_one)) in
                                     FStar_All.pipe_right uu____9660
                                       (fun uu____9872 ->
                                          match uu____9872 with
                                          | (l1, l2) ->
                                              let uu____10023 =
                                                FStar_List.hd l2 in
                                              (l1, uu____10023)) in
                                   (match uu____9621 with
                                    | (lcases1,
                                       (g_last, eff_last, uu____10125,
                                        c_last)) ->
                                        let uu____10195 =
                                          let lc =
                                            maybe_return eff_last c_last in
                                          let uu____10201 =
                                            FStar_TypeChecker_Common.lcomp_comp
                                              lc in
                                          match uu____10201 with
                                          | (c, g) ->
                                              let uu____10212 =
                                                let uu____10213 =
                                                  FStar_Syntax_Util.mk_conj
                                                    g_last neg_last in
                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                  g uu____10213 in
                                              (c, uu____10212) in
                                        (match uu____10195 with
                                         | (c, g) ->
                                             let uu____10248 =
                                               let uu____10249 =
                                                 FStar_All.pipe_right
                                                   eff_last
                                                   (FStar_TypeChecker_Env.norm_eff_name
                                                      env) in
                                               FStar_All.pipe_right
                                                 uu____10249
                                                 (FStar_TypeChecker_Env.get_effect_decl
                                                    env) in
                                             (lcases1, neg_branch_conds1,
                                               uu____10248, c, g))) in
                             (match uu____9407 with
                              | (lcases1, neg_branch_conds1, md, comp,
                                 g_comp) ->
                                  FStar_List.fold_right2
                                    (fun uu____10381 ->
                                       fun neg_cond ->
                                         fun uu____10383 ->
                                           match (uu____10381, uu____10383)
                                           with
                                           | ((g, eff_label, uu____10443,
                                               cthen),
                                              (uu____10445, celse, g_comp1))
                                               ->
                                               let uu____10492 =
                                                 let uu____10497 =
                                                   maybe_return eff_label
                                                     cthen in
                                                 FStar_TypeChecker_Common.lcomp_comp
                                                   uu____10497 in
                                               (match uu____10492 with
                                                | (cthen1, g_then) ->
                                                    let uu____10508 =
                                                      let uu____10519 =
                                                        lift_comps_sep_guards
                                                          env cthen1 celse
                                                          FStar_Pervasives_Native.None
                                                          false in
                                                      match uu____10519 with
                                                      | (m, cthen2, celse1,
                                                         g_lift_then,
                                                         g_lift_else) ->
                                                          let md1 =
                                                            FStar_TypeChecker_Env.get_effect_decl
                                                              env m in
                                                          let uu____10547 =
                                                            FStar_All.pipe_right
                                                              cthen2
                                                              FStar_Syntax_Util.comp_to_comp_typ in
                                                          let uu____10548 =
                                                            FStar_All.pipe_right
                                                              celse1
                                                              FStar_Syntax_Util.comp_to_comp_typ in
                                                          (md1, uu____10547,
                                                            uu____10548,
                                                            g_lift_then,
                                                            g_lift_else) in
                                                    (match uu____10508 with
                                                     | (md1, ct_then,
                                                        ct_else, g_lift_then,
                                                        g_lift_else) ->
                                                         let fn =
                                                           let uu____10599 =
                                                             FStar_All.pipe_right
                                                               md1
                                                               FStar_Syntax_Util.is_layered in
                                                           if uu____10599
                                                           then
                                                             mk_layered_conjunction
                                                           else
                                                             mk_non_layered_conjunction in
                                                         let uu____10633 =
                                                           let uu____10638 =
                                                             FStar_TypeChecker_Env.get_range
                                                               env in
                                                           fn env md1 u_res_t
                                                             res_t g ct_then
                                                             ct_else
                                                             uu____10638 in
                                                         (match uu____10633
                                                          with
                                                          | (c,
                                                             g_conjunction)
                                                              ->
                                                              let g_then1 =
                                                                let uu____10650
                                                                  =
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_then
                                                                    g_lift_then in
                                                                let uu____10651
                                                                  =
                                                                  FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    g in
                                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                                  uu____10650
                                                                  uu____10651 in
                                                              let g_else =
                                                                let uu____10653
                                                                  =
                                                                  let uu____10654
                                                                    =
                                                                    FStar_Syntax_Util.mk_neg
                                                                    g in
                                                                  FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    uu____10654 in
                                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                                  g_lift_else
                                                                  uu____10653 in
                                                              let uu____10657
                                                                =
                                                                FStar_TypeChecker_Env.conj_guards
                                                                  [g_comp1;
                                                                  g_then1;
                                                                  g_else;
                                                                  g_conjunction] in
                                                              ((FStar_Pervasives_Native.Some
                                                                  md1), c,
                                                                uu____10657)))))
                                    lcases1 neg_branch_conds1
                                    ((FStar_Pervasives_Native.Some md), comp,
                                      g_comp)) in
                       (match uu____9356 with
                        | (md, comp, g_comp) ->
                            let uu____10673 =
                              let uu____10678 =
                                let check =
                                  FStar_Syntax_Util.mk_imp
                                    exhaustiveness_branch_cond
                                    FStar_Syntax_Util.t_false in
                                let check1 =
                                  let uu____10685 =
                                    FStar_TypeChecker_Env.get_range env in
                                  label
                                    FStar_TypeChecker_Err.exhaustiveness_check
                                    uu____10685 check in
                                strengthen_comp env
                                  FStar_Pervasives_Native.None comp check1
                                  bind_cases_flags in
                              match uu____10678 with
                              | (c, g) ->
                                  let uu____10696 =
                                    FStar_TypeChecker_Env.conj_guard g_comp g in
                                  (c, uu____10696) in
                            (match uu____10673 with
                             | (comp1, g_comp1) ->
                                 let g_comp2 =
                                   let uu____10704 =
                                     let uu____10705 =
                                       FStar_All.pipe_right scrutinee
                                         FStar_Syntax_Syntax.mk_binder in
                                     [uu____10705] in
                                   FStar_TypeChecker_Env.close_guard env0
                                     uu____10704 g_comp1 in
                                 (match lcases with
                                  | [] -> (comp1, g_comp2)
                                  | uu____10748::[] -> (comp1, g_comp2)
                                  | uu____10791 ->
                                      let uu____10808 =
                                        let uu____10810 =
                                          FStar_All.pipe_right md
                                            FStar_Util.must in
                                        FStar_All.pipe_right uu____10810
                                          FStar_Syntax_Util.is_layered in
                                      if uu____10808
                                      then (comp1, g_comp2)
                                      else
                                        (let comp2 =
                                           FStar_TypeChecker_Env.comp_to_comp_typ
                                             env comp1 in
                                         let md1 =
                                           FStar_TypeChecker_Env.get_effect_decl
                                             env
                                             comp2.FStar_Syntax_Syntax.effect_name in
                                         let uu____10823 =
                                           destruct_wp_comp comp2 in
                                         match uu____10823 with
                                         | (uu____10834, uu____10835, wp) ->
                                             let ite_wp =
                                               let uu____10838 =
                                                 FStar_All.pipe_right md1
                                                   FStar_Syntax_Util.get_wp_ite_combinator in
                                               FStar_All.pipe_right
                                                 uu____10838 FStar_Util.must in
                                             let wp1 =
                                               let uu____10846 =
                                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                                   [u_res_t] env md1 ite_wp in
                                               let uu____10847 =
                                                 let uu____10848 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     res_t in
                                                 let uu____10857 =
                                                   let uu____10868 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp in
                                                   [uu____10868] in
                                                 uu____10848 :: uu____10857 in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu____10846 uu____10847
                                                 wp.FStar_Syntax_Syntax.pos in
                                             let uu____10901 =
                                               mk_comp md1 u_res_t res_t wp1
                                                 bind_cases_flags in
                                             (uu____10901, g_comp2)))))) in
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
          let uu____10936 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____10936 with
          | FStar_Pervasives_Native.None ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____10952 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c' in
                let uu____10958 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error uu____10952 uu____10958
              else
                (let uu____10967 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c' in
                 let uu____10973 = FStar_TypeChecker_Env.get_range env in
                 FStar_Errors.raise_error uu____10967 uu____10973)
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
          let uu____10998 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name in
          FStar_All.pipe_right uu____10998
            (FStar_TypeChecker_Env.norm_eff_name env) in
        let uu____11001 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid in
        if uu____11001
        then u_res
        else
          (let is_total =
             let uu____11008 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid in
             FStar_All.pipe_right uu____11008
               (FStar_List.existsb
                  (fun q -> q = FStar_Syntax_Syntax.TotalEffect)) in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____11019 = FStar_TypeChecker_Env.effect_repr env c u_res in
              match uu____11019 with
              | FStar_Pervasives_Native.None ->
                  let uu____11022 =
                    let uu____11028 =
                      let uu____11030 =
                        FStar_Syntax_Print.lid_to_string c_lid in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____11030 in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____11028) in
                  FStar_Errors.raise_error uu____11022
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
      let uu____11054 = destruct_wp_comp ct in
      match uu____11054 with
      | (u_t, t, wp) ->
          let vc =
            let uu____11071 =
              let uu____11072 =
                let uu____11073 =
                  FStar_All.pipe_right md
                    FStar_Syntax_Util.get_wp_trivial_combinator in
                FStar_All.pipe_right uu____11073 FStar_Util.must in
              FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                uu____11072 in
            let uu____11080 =
              let uu____11081 = FStar_Syntax_Syntax.as_arg t in
              let uu____11090 =
                let uu____11101 = FStar_Syntax_Syntax.as_arg wp in
                [uu____11101] in
              uu____11081 :: uu____11090 in
            let uu____11134 = FStar_TypeChecker_Env.get_range env in
            FStar_Syntax_Syntax.mk_Tm_app uu____11071 uu____11080 uu____11134 in
          let uu____11135 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc) in
          (ct, vc, uu____11135)
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
                  let uu____11190 =
                    FStar_TypeChecker_Env.try_lookup_lid env f in
                  match uu____11190 with
                  | FStar_Pervasives_Native.Some uu____11205 ->
                      ((let uu____11223 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions") in
                        if uu____11223
                        then
                          let uu____11227 = FStar_Ident.string_of_lid f in
                          FStar_Util.print1 "Coercing with %s!\n" uu____11227
                        else ());
                       (let coercion =
                          let uu____11233 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos in
                          FStar_Syntax_Syntax.fvar uu____11233
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs in
                        let lc1 =
                          let uu____11240 =
                            let uu____11241 =
                              let uu____11242 = mkcomp ty in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____11242 in
                            (FStar_Pervasives_Native.None, uu____11241) in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____11240 in
                        let e1 =
                          let uu____11246 =
                            let uu____11247 = FStar_Syntax_Syntax.as_arg e in
                            [uu____11247] in
                          FStar_Syntax_Syntax.mk_Tm_app coercion2 uu____11246
                            e.FStar_Syntax_Syntax.pos in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None ->
                      ((let uu____11281 =
                          let uu____11287 =
                            let uu____11289 = FStar_Ident.string_of_lid f in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____11289 in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____11287) in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____11281);
                       (e, lc))
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee ->
    match projectee with | Yes _0 -> true | uu____11308 -> false
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee -> match projectee with | Yes _0 -> _0
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee ->
    match projectee with | Maybe -> true | uu____11326 -> false
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee -> match projectee with | No -> true | uu____11337 -> false
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
      let uu____11361 = FStar_Syntax_Util.head_and_args t2 in
      match uu____11361 with
      | (h, args) ->
          let h1 = FStar_Syntax_Util.un_uinst h in
          let r =
            let uu____11406 =
              let uu____11421 =
                let uu____11422 = FStar_Syntax_Subst.compress h1 in
                uu____11422.FStar_Syntax_Syntax.n in
              (uu____11421, args) in
            match uu____11406 with
            | (FStar_Syntax_Syntax.Tm_fvar fv,
               (a, FStar_Pervasives_Native.None)::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____11469, uu____11470) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown, uu____11503) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match (uu____11524, branches),
               uu____11526) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc ->
                        fun br ->
                          match acc with
                          | Yes uu____11590 -> Maybe
                          | Maybe -> Maybe
                          | No ->
                              let uu____11591 =
                                FStar_Syntax_Subst.open_branch br in
                              (match uu____11591 with
                               | (uu____11592, uu____11593, br_body) ->
                                   let uu____11611 =
                                     let uu____11612 =
                                       let uu____11617 =
                                         let uu____11618 =
                                           let uu____11621 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names in
                                           FStar_All.pipe_right uu____11621
                                             FStar_Util.set_elements in
                                         FStar_All.pipe_right uu____11618
                                           (FStar_TypeChecker_Env.push_bvs
                                              env) in
                                       check_erased uu____11617 in
                                     FStar_All.pipe_right br_body uu____11612 in
                                   (match uu____11611 with
                                    | No -> No
                                    | uu____11632 -> Maybe))) No)
            | uu____11633 -> No in
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
            (((let uu____11685 = FStar_Options.use_two_phase_tc () in
               Prims.op_Negation uu____11685) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ()) in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
               let uu____11704 =
                 let uu____11705 = FStar_Syntax_Subst.compress t1 in
                 uu____11705.FStar_Syntax_Syntax.n in
               match uu____11704 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____11710 -> false in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
               let uu____11720 =
                 let uu____11721 = FStar_Syntax_Subst.compress t1 in
                 uu____11721.FStar_Syntax_Syntax.n in
               match uu____11720 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____11726 -> false in
             let is_type t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
               let t2 = FStar_Syntax_Util.unrefine t1 in
               let uu____11737 =
                 let uu____11738 = FStar_Syntax_Subst.compress t2 in
                 uu____11738.FStar_Syntax_Syntax.n in
               match uu____11737 with
               | FStar_Syntax_Syntax.Tm_type uu____11742 -> true
               | uu____11744 -> false in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ in
             let uu____11747 = FStar_Syntax_Util.head_and_args res_typ in
             match uu____11747 with
             | (head, args) ->
                 ((let uu____11797 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions") in
                   if uu____11797
                   then
                     let uu____11801 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                     let uu____11803 = FStar_Syntax_Print.term_to_string e in
                     let uu____11805 =
                       FStar_Syntax_Print.term_to_string res_typ in
                     let uu____11807 =
                       FStar_Syntax_Print.term_to_string exp_t in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____11801 uu____11803 uu____11805 uu____11807
                   else ());
                  (let mk_erased u t =
                     let uu____11825 =
                       let uu____11828 =
                         fvar_const env FStar_Parser_Const.erased_lid in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____11828 [u] in
                     let uu____11829 =
                       let uu____11840 = FStar_Syntax_Syntax.as_arg t in
                       [uu____11840] in
                     FStar_Syntax_Util.mk_app uu____11825 uu____11829 in
                   let uu____11865 =
                     let uu____11880 =
                       let uu____11881 = FStar_Syntax_Util.un_uinst head in
                       uu____11881.FStar_Syntax_Syntax.n in
                     (uu____11880, args) in
                   match uu____11865 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type exp_t)
                       ->
                       let uu____11919 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total in
                       (match uu____11919 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____11959 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac in
                       (match uu____11959 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11999 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac in
                       (match uu____11999 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____12039 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac in
                       (match uu____12039 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____12060 ->
                       let uu____12075 =
                         let uu____12080 = check_erased env res_typ in
                         let uu____12081 = check_erased env exp_t in
                         (uu____12080, uu____12081) in
                       (match uu____12075 with
                        | (No, Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty in
                            let uu____12090 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty in
                            (match uu____12090 with
                             | FStar_Pervasives_Native.None ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e in
                                 let uu____12101 =
                                   let uu____12106 =
                                     let uu____12107 =
                                       FStar_Syntax_Syntax.iarg ty in
                                     [uu____12107] in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____12106
                                     FStar_Syntax_Syntax.mk_Total in
                                 (match uu____12101 with
                                  | (e1, lc1) -> (e1, lc1, g1)))
                        | (Yes ty, No) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty in
                            let uu____12142 =
                              let uu____12147 =
                                let uu____12148 = FStar_Syntax_Syntax.iarg ty in
                                [uu____12148] in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____12147
                                FStar_Syntax_Syntax.mk_GTotal in
                            (match uu____12142 with
                             | (e1, lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____12181 ->
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
        let uu____12216 = FStar_Syntax_Util.head_and_args rt1 in
        match uu____12216 with
        | (hd, args) ->
            let uu____12265 =
              let uu____12280 =
                let uu____12281 = FStar_Syntax_Subst.compress hd in
                uu____12281.FStar_Syntax_Syntax.n in
              (uu____12280, args) in
            (match uu____12265 with
             | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____12319 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac in
                 FStar_All.pipe_left
                   (fun uu____12346 ->
                      FStar_Pervasives_Native.Some uu____12346) uu____12319
             | uu____12347 -> FStar_Pervasives_Native.None)
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
          (let uu____12400 =
             FStar_TypeChecker_Env.debug env FStar_Options.High in
           if uu____12400
           then
             let uu____12403 = FStar_Syntax_Print.term_to_string e in
             let uu____12405 = FStar_TypeChecker_Common.lcomp_to_string lc in
             let uu____12407 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____12403 uu____12405 uu____12407
           else ());
          (let use_eq =
             (env.FStar_TypeChecker_Env.use_eq_strict ||
                env.FStar_TypeChecker_Env.use_eq)
               ||
               (let uu____12417 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name in
                match uu____12417 with
                | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____12442 -> false) in
           let gopt =
             if use_eq
             then
               let uu____12468 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t in
               (uu____12468, false)
             else
               (let uu____12478 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t in
                (uu____12478, true)) in
           match gopt with
           | (FStar_Pervasives_Native.None, uu____12491) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____12503 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ in
                 FStar_Errors.raise_error uu____12503
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1397_12519 = lc in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1397_12519.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1397_12519.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1397_12519.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g, apply_guard) ->
               let uu____12526 = FStar_TypeChecker_Env.guard_form g in
               (match uu____12526 with
                | FStar_TypeChecker_Common.Trivial ->
                    let strengthen_trivial uu____12542 =
                      let uu____12543 =
                        FStar_TypeChecker_Common.lcomp_comp lc in
                      match uu____12543 with
                      | (c, g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c in
                          let set_result_typ c1 =
                            FStar_Syntax_Util.set_result_typ c1 t in
                          let uu____12563 =
                            let uu____12565 = FStar_Syntax_Util.eq_tm t res_t in
                            uu____12565 = FStar_Syntax_Util.Equal in
                          if uu____12563
                          then
                            ((let uu____12572 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____12572
                              then
                                let uu____12576 =
                                  FStar_Syntax_Print.term_to_string res_t in
                                let uu____12578 =
                                  FStar_Syntax_Print.term_to_string t in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____12576 uu____12578
                              else ());
                             (let uu____12583 = set_result_typ c in
                              (uu____12583, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____12590 ->
                                   true
                               | uu____12598 -> false in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t in
                               let uu____12606 =
                                 let uu____12611 =
                                   let uu____12612 =
                                     FStar_All.pipe_right c
                                       FStar_Syntax_Util.comp_effect_name in
                                   FStar_All.pipe_right uu____12612
                                     (FStar_TypeChecker_Env.norm_eff_name env) in
                                 let uu____12615 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env uu____12611
                                   (comp_univ_opt c) res_t uu____12615 in
                               match uu____12606 with
                               | (cret, gret) ->
                                   let lc1 =
                                     let uu____12625 =
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                         c in
                                     let uu____12626 =
                                       let uu____12627 =
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                           cret in
                                       ((FStar_Pervasives_Native.Some x),
                                         uu____12627) in
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (FStar_Pervasives_Native.Some e)
                                       uu____12625 uu____12626 in
                                   ((let uu____12631 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme in
                                     if uu____12631
                                     then
                                       let uu____12635 =
                                         FStar_Syntax_Print.term_to_string e in
                                       let uu____12637 =
                                         FStar_Syntax_Print.comp_to_string c in
                                       let uu____12639 =
                                         FStar_Syntax_Print.term_to_string t in
                                       let uu____12641 =
                                         FStar_TypeChecker_Common.lcomp_to_string
                                           lc1 in
                                       FStar_Util.print4
                                         "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                         uu____12635 uu____12637 uu____12639
                                         uu____12641
                                     else ());
                                    (let uu____12646 =
                                       FStar_TypeChecker_Common.lcomp_comp
                                         lc1 in
                                     match uu____12646 with
                                     | (c1, g_lc) ->
                                         let uu____12657 = set_result_typ c1 in
                                         let uu____12658 =
                                           FStar_TypeChecker_Env.conj_guards
                                             [g_c; gret; g_lc] in
                                         (uu____12657, uu____12658)))
                             else
                               ((let uu____12662 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____12662
                                 then
                                   let uu____12666 =
                                     FStar_Syntax_Print.term_to_string res_t in
                                   let uu____12668 =
                                     FStar_Syntax_Print.comp_to_string c in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____12666 uu____12668
                                 else ());
                                (let uu____12673 = set_result_typ c in
                                 (uu____12673, g_c)))) in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1436_12677 = g in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred_to_tac =
                          (uu___1436_12677.FStar_TypeChecker_Common.deferred_to_tac);
                        FStar_TypeChecker_Common.deferred =
                          (uu___1436_12677.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1436_12677.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1436_12677.FStar_TypeChecker_Common.implicits)
                      } in
                    let strengthen uu____12687 =
                      let uu____12688 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ()) in
                      if uu____12688
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f in
                         let uu____12698 =
                           let uu____12699 = FStar_Syntax_Subst.compress f1 in
                           uu____12699.FStar_Syntax_Syntax.n in
                         match uu____12698 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____12706,
                              {
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Tm_fvar fv;
                                FStar_Syntax_Syntax.pos = uu____12708;
                                FStar_Syntax_Syntax.vars = uu____12709;_},
                              uu____12710)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1452_12736 = lc in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1452_12736.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1452_12736.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1452_12736.FStar_TypeChecker_Common.comp_thunk)
                               } in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____12737 ->
                             let uu____12738 =
                               FStar_TypeChecker_Common.lcomp_comp lc in
                             (match uu____12738 with
                              | (c, g_c) ->
                                  ((let uu____12750 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme in
                                    if uu____12750
                                    then
                                      let uu____12754 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ in
                                      let uu____12756 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t in
                                      let uu____12758 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c in
                                      let uu____12760 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1 in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____12754 uu____12756 uu____12758
                                        uu____12760
                                    else ());
                                   (let u_t_opt = comp_univ_opt c in
                                    let x =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (t.FStar_Syntax_Syntax.pos)) t in
                                    let xexp =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____12770 =
                                      let uu____12775 =
                                        let uu____12776 =
                                          FStar_All.pipe_right c
                                            FStar_Syntax_Util.comp_effect_name in
                                        FStar_All.pipe_right uu____12776
                                          (FStar_TypeChecker_Env.norm_eff_name
                                             env) in
                                      return_value env uu____12775 u_t_opt t
                                        xexp in
                                    match uu____12770 with
                                    | (cret, gret) ->
                                        let guard =
                                          if apply_guard
                                          then
                                            let uu____12787 =
                                              let uu____12788 =
                                                FStar_Syntax_Syntax.as_arg
                                                  xexp in
                                              [uu____12788] in
                                            FStar_Syntax_Syntax.mk_Tm_app f1
                                              uu____12787
                                              f1.FStar_Syntax_Syntax.pos
                                          else f1 in
                                        let uu____12815 =
                                          let uu____12820 =
                                            FStar_All.pipe_left
                                              (fun uu____12841 ->
                                                 FStar_Pervasives_Native.Some
                                                   uu____12841)
                                              (FStar_TypeChecker_Err.subtyping_failed
                                                 env
                                                 lc.FStar_TypeChecker_Common.res_typ
                                                 t) in
                                          let uu____12842 =
                                            let uu____12843 =
                                              FStar_TypeChecker_Env.push_bvs
                                                env [x] in
                                            FStar_TypeChecker_Env.set_range
                                              uu____12843
                                              e.FStar_Syntax_Syntax.pos in
                                          let uu____12844 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              cret in
                                          let uu____12845 =
                                            FStar_All.pipe_left
                                              FStar_TypeChecker_Env.guard_of_guard_formula
                                              (FStar_TypeChecker_Common.NonTrivial
                                                 guard) in
                                          strengthen_precondition uu____12820
                                            uu____12842 e uu____12844
                                            uu____12845 in
                                        (match uu____12815 with
                                         | (eq_ret,
                                            _trivial_so_ok_to_discard) ->
                                             let x1 =
                                               let uu___1472_12853 = x in
                                               {
                                                 FStar_Syntax_Syntax.ppname =
                                                   (uu___1472_12853.FStar_Syntax_Syntax.ppname);
                                                 FStar_Syntax_Syntax.index =
                                                   (uu___1472_12853.FStar_Syntax_Syntax.index);
                                                 FStar_Syntax_Syntax.sort =
                                                   (lc.FStar_TypeChecker_Common.res_typ)
                                               } in
                                             let c1 =
                                               let uu____12855 =
                                                 FStar_TypeChecker_Common.lcomp_of_comp
                                                   c in
                                               bind e.FStar_Syntax_Syntax.pos
                                                 env
                                                 (FStar_Pervasives_Native.Some
                                                    e) uu____12855
                                                 ((FStar_Pervasives_Native.Some
                                                     x1), eq_ret) in
                                             let uu____12858 =
                                               FStar_TypeChecker_Common.lcomp_comp
                                                 c1 in
                                             (match uu____12858 with
                                              | (c2, g_lc) ->
                                                  ((let uu____12870 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        FStar_Options.Extreme in
                                                    if uu____12870
                                                    then
                                                      let uu____12874 =
                                                        FStar_TypeChecker_Normalize.comp_to_string
                                                          env c2 in
                                                      FStar_Util.print1
                                                        "Strengthened to %s\n"
                                                        uu____12874
                                                    else ());
                                                   (let uu____12879 =
                                                      FStar_TypeChecker_Env.conj_guards
                                                        [g_c; gret; g_lc] in
                                                    (c2, uu____12879))))))))) in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_12888 ->
                              match uu___6_12888 with
                              | FStar_Syntax_Syntax.RETURN ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____12891 -> [])) in
                    let lc1 =
                      let uu____12893 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name in
                      FStar_TypeChecker_Common.mk_lcomp uu____12893 t flags
                        strengthen in
                    let g2 =
                      let uu___1488_12895 = g1 in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred_to_tac =
                          (uu___1488_12895.FStar_TypeChecker_Common.deferred_to_tac);
                        FStar_TypeChecker_Common.deferred =
                          (uu___1488_12895.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1488_12895.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1488_12895.FStar_TypeChecker_Common.implicits)
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
        let uu____12931 =
          let uu____12934 =
            let uu____12935 =
              let uu____12944 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_Syntax_Syntax.as_arg uu____12944 in
            [uu____12935] in
          FStar_Syntax_Syntax.mk_Tm_app ens uu____12934
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____12931 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t in
      let uu____12967 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____12967
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____12986 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____13002 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____13019 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid) in
             if uu____13019
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req, uu____13035)::(ens, uu____13037)::uu____13038 ->
                    let uu____13081 =
                      let uu____13084 = norm req in
                      FStar_Pervasives_Native.Some uu____13084 in
                    let uu____13085 =
                      let uu____13086 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____13086 in
                    (uu____13081, uu____13085)
                | uu____13089 ->
                    let uu____13100 =
                      let uu____13106 =
                        let uu____13108 =
                          FStar_Syntax_Print.comp_to_string comp in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____13108 in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____13106) in
                    FStar_Errors.raise_error uu____13100
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp, uu____13128)::uu____13129 ->
                    let uu____13156 =
                      let uu____13161 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____13161 in
                    (match uu____13156 with
                     | (us_r, uu____13193) ->
                         let uu____13194 =
                           let uu____13199 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____13199 in
                         (match uu____13194 with
                          | (us_e, uu____13231) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____13234 =
                                  let uu____13235 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r in
                                  FStar_Syntax_Syntax.fvar uu____13235
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____13234
                                  us_r in
                              let as_ens =
                                let uu____13237 =
                                  let uu____13238 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r in
                                  FStar_Syntax_Syntax.fvar uu____13238
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____13237
                                  us_e in
                              let req =
                                let uu____13240 =
                                  let uu____13241 =
                                    let uu____13252 =
                                      FStar_Syntax_Syntax.as_arg wp in
                                    [uu____13252] in
                                  ((ct1.FStar_Syntax_Syntax.result_typ),
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.imp_tag))
                                    :: uu____13241 in
                                FStar_Syntax_Syntax.mk_Tm_app as_req
                                  uu____13240
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____13290 =
                                  let uu____13291 =
                                    let uu____13302 =
                                      FStar_Syntax_Syntax.as_arg wp in
                                    [uu____13302] in
                                  ((ct1.FStar_Syntax_Syntax.result_typ),
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.imp_tag))
                                    :: uu____13291 in
                                FStar_Syntax_Syntax.mk_Tm_app as_ens
                                  uu____13290
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____13339 =
                                let uu____13342 = norm req in
                                FStar_Pervasives_Native.Some uu____13342 in
                              let uu____13343 =
                                let uu____13344 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____13344 in
                              (uu____13339, uu____13343)))
                | uu____13347 -> failwith "Impossible"))
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
        (let uu____13386 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____13386
         then
           let uu____13391 = FStar_Syntax_Print.term_to_string tm in
           let uu____13393 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____13391
             uu____13393
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
          (let uu____13452 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify") in
           if uu____13452
           then
             let uu____13457 = FStar_Syntax_Print.term_to_string tm in
             let uu____13459 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____13457
               uu____13459
           else ());
          tm'
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____13470 =
      let uu____13472 =
        let uu____13473 = FStar_Syntax_Subst.compress t in
        uu____13473.FStar_Syntax_Syntax.n in
      match uu____13472 with
      | FStar_Syntax_Syntax.Tm_app uu____13477 -> false
      | uu____13495 -> true in
    if uu____13470
    then t
    else
      (let uu____13500 = FStar_Syntax_Util.head_and_args t in
       match uu____13500 with
       | (head, args) ->
           let uu____13543 =
             let uu____13545 =
               let uu____13546 = FStar_Syntax_Subst.compress head in
               uu____13546.FStar_Syntax_Syntax.n in
             match uu____13545 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) ->
                 true
             | uu____13551 -> false in
           if uu____13543
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____13583 ->
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
          ((let uu____13630 =
              FStar_TypeChecker_Env.debug env FStar_Options.High in
            if uu____13630
            then
              let uu____13633 = FStar_Syntax_Print.term_to_string e in
              let uu____13635 = FStar_Syntax_Print.term_to_string t in
              let uu____13637 =
                let uu____13639 = FStar_TypeChecker_Env.expected_typ env in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____13639 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____13633 uu____13635 uu____13637
            else ());
           (let unfolded_arrow_formals t1 =
              let rec aux bs t2 =
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf env t2 in
                let uu____13675 = FStar_Syntax_Util.arrow_formals t3 in
                match uu____13675 with
                | (bs', t4) ->
                    (match bs' with
                     | [] -> bs
                     | bs'1 -> aux (FStar_List.append bs bs'1) t4) in
              aux [] t1 in
            let number_of_implicits t1 =
              let formals = unfolded_arrow_formals t1 in
              let n_implicits =
                let uu____13709 =
                  FStar_All.pipe_right formals
                    (FStar_Util.prefix_until
                       (fun uu____13787 ->
                          match uu____13787 with
                          | (uu____13795, imp) ->
                              (FStar_Option.isNone imp) ||
                                (let uu____13802 =
                                   FStar_Syntax_Util.eq_aqual imp
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Equality) in
                                 uu____13802 = FStar_Syntax_Util.Equal))) in
                match uu____13709 with
                | FStar_Pervasives_Native.None -> FStar_List.length formals
                | FStar_Pervasives_Native.Some
                    (implicits, _first_explicit, _rest) ->
                    FStar_List.length implicits in
              n_implicits in
            let inst_n_binders t1 =
              let uu____13921 = FStar_TypeChecker_Env.expected_typ env in
              match uu____13921 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t in
                  let n_available = number_of_implicits t1 in
                  if n_available < n_expected
                  then
                    let uu____13935 =
                      let uu____13941 =
                        let uu____13943 = FStar_Util.string_of_int n_expected in
                        let uu____13945 = FStar_Syntax_Print.term_to_string e in
                        let uu____13947 =
                          FStar_Util.string_of_int n_available in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____13943 uu____13945 uu____13947 in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____13941) in
                    let uu____13951 = FStar_TypeChecker_Env.get_range env in
                    FStar_Errors.raise_error uu____13935 uu____13951
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected) in
            let decr_inst uu___7_13969 =
              match uu___7_13969 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one) in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                let uu____14012 = FStar_Syntax_Subst.open_comp bs c in
                (match uu____14012 with
                 | (bs1, c1) ->
                     let rec aux subst inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some uu____14143,
                          uu____14130) when uu____14143 = Prims.int_zero ->
                           ([], bs2, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____14176,
                          (x, FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit uu____14178))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort in
                           let uu____14212 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2 in
                           (match uu____14212 with
                            | (v, uu____14253, g) ->
                                ((let uu____14268 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High in
                                  if uu____14268
                                  then
                                    let uu____14271 =
                                      FStar_Syntax_Print.term_to_string v in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____14271
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst in
                                  let uu____14281 =
                                    aux subst1 (decr_inst inst_n) rest in
                                  match uu____14281 with
                                  | (args, bs3, subst2, g') ->
                                      let uu____14374 =
                                        FStar_TypeChecker_Env.conj_guard g g' in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____14374))))
                       | (uu____14401,
                          (x, FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tac_or_attr))::rest) ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort in
                           let meta_t =
                             match tac_or_attr with
                             | FStar_Syntax_Syntax.Arg_qualifier_meta_tac tau
                                 ->
                                 let uu____14440 =
                                   let uu____14447 = FStar_Dyn.mkdyn env in
                                   (uu____14447, tau) in
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   uu____14440
                             | FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                 attr ->
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_attr attr in
                           let uu____14453 =
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict
                               (FStar_Pervasives_Native.Some meta_t) in
                           (match uu____14453 with
                            | (v, uu____14494, g) ->
                                ((let uu____14509 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High in
                                  if uu____14509
                                  then
                                    let uu____14512 =
                                      FStar_Syntax_Print.term_to_string v in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____14512
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst in
                                  let uu____14522 =
                                    aux subst1 (decr_inst inst_n) rest in
                                  match uu____14522 with
                                  | (args, bs3, subst2, g') ->
                                      let uu____14615 =
                                        FStar_TypeChecker_Env.conj_guard g g' in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____14615))))
                       | (uu____14642, bs3) ->
                           ([], bs3, subst,
                             FStar_TypeChecker_Env.trivial_guard) in
                     let uu____14690 =
                       let uu____14717 = inst_n_binders t1 in
                       aux [] uu____14717 bs1 in
                     (match uu____14690 with
                      | (args, bs2, subst, guard) ->
                          (match (args, bs2) with
                           | ([], uu____14789) -> (e, torig, guard)
                           | (uu____14820, []) when
                               let uu____14851 =
                                 FStar_Syntax_Util.is_total_comp c1 in
                               Prims.op_Negation uu____14851 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____14853 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____14881 ->
                                     FStar_Syntax_Util.arrow bs2 c1 in
                               let t3 = FStar_Syntax_Subst.subst subst t2 in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   e.FStar_Syntax_Syntax.pos in
                               (e1, t3, guard))))
            | uu____14892 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs ->
    let uu____14904 =
      let uu____14908 = FStar_Util.set_elements univs in
      FStar_All.pipe_right uu____14908
        (FStar_List.map
           (fun u ->
              let uu____14920 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____14920 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____14904 (FStar_String.concat ", ")
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env ->
    fun x ->
      let uu____14948 = FStar_Util.set_is_empty x in
      if uu____14948
      then []
      else
        (let s =
           let uu____14968 =
             let uu____14971 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____14971 in
           FStar_All.pipe_right uu____14968 FStar_Util.set_elements in
         (let uu____14989 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____14989
          then
            let uu____14994 =
              let uu____14996 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____14996 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____14994
          else ());
         (let r =
            let uu____15005 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____15005 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____15050 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____15050
                     then
                       let uu____15055 =
                         let uu____15057 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____15057 in
                       let uu____15061 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____15063 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____15055 uu____15061 uu____15063
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
        let uu____15093 =
          FStar_Util.set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____15093 FStar_Util.set_elements in
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
        | ([], uu____15132) -> generalized_univ_names
        | (uu____15139, []) -> explicit_univ_names
        | uu____15146 ->
            let uu____15155 =
              let uu____15161 =
                let uu____15163 = FStar_Syntax_Print.term_to_string t in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____15163 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____15161) in
            FStar_Errors.raise_error uu____15155 t.FStar_Syntax_Syntax.pos
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
      (let uu____15185 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____15185
       then
         let uu____15190 = FStar_Syntax_Print.term_to_string t in
         let uu____15192 = FStar_Syntax_Print.univ_names_to_string univnames in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____15190 uu____15192
       else ());
      (let univs = FStar_Syntax_Free.univs t in
       (let uu____15201 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____15201
        then
          let uu____15206 = string_of_univs univs in
          FStar_Util.print1 "univs to gen : %s\n" uu____15206
        else ());
       (let gen = gen_univs env univs in
        (let uu____15215 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen") in
         if uu____15215
         then
           let uu____15220 = FStar_Syntax_Print.term_to_string t in
           let uu____15222 = FStar_Syntax_Print.univ_names_to_string gen in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____15220 uu____15222
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
        let uu____15306 =
          let uu____15308 =
            FStar_Util.for_all
              (fun uu____15322 ->
                 match uu____15322 with
                 | (uu____15332, uu____15333, c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          FStar_All.pipe_left Prims.op_Negation uu____15308 in
        if uu____15306
        then FStar_Pervasives_Native.None
        else
          (let norm c =
             (let uu____15385 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              if uu____15385
              then
                let uu____15388 = FStar_Syntax_Print.comp_to_string c in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____15388
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c in
              (let uu____15395 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____15395
               then
                 let uu____15398 = FStar_Syntax_Print.comp_to_string c1 in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____15398
               else ());
              c1) in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu____15416 = FStar_Util.set_difference uvs env_uvars in
             FStar_All.pipe_right uu____15416 FStar_Util.set_elements in
           let univs_and_uvars_of_lec uu____15450 =
             match uu____15450 with
             | (lbname, e, c) ->
                 let c1 = norm c in
                 let t = FStar_Syntax_Util.comp_result c1 in
                 let univs = FStar_Syntax_Free.univs t in
                 let uvt = FStar_Syntax_Free.uvars t in
                 ((let uu____15487 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen") in
                   if uu____15487
                   then
                     let uu____15492 =
                       let uu____15494 =
                         let uu____15498 = FStar_Util.set_elements univs in
                         FStar_All.pipe_right uu____15498
                           (FStar_List.map
                              (fun u ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u))) in
                       FStar_All.pipe_right uu____15494
                         (FStar_String.concat ", ") in
                     let uu____15554 =
                       let uu____15556 =
                         let uu____15560 = FStar_Util.set_elements uvt in
                         FStar_All.pipe_right uu____15560
                           (FStar_List.map
                              (fun u ->
                                 let uu____15573 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head in
                                 let uu____15575 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                 FStar_Util.format2 "(%s : %s)" uu____15573
                                   uu____15575)) in
                       FStar_All.pipe_right uu____15556
                         (FStar_String.concat ", ") in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____15492
                       uu____15554
                   else ());
                  (let univs1 =
                     let uu____15589 = FStar_Util.set_elements uvt in
                     FStar_List.fold_left
                       (fun univs1 ->
                          fun uv ->
                            let uu____15601 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ in
                            FStar_Util.set_union univs1 uu____15601) univs
                       uu____15589 in
                   let uvs = gen_uvars uvt in
                   (let uu____15608 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen") in
                    if uu____15608
                    then
                      let uu____15613 =
                        let uu____15615 =
                          let uu____15619 = FStar_Util.set_elements univs1 in
                          FStar_All.pipe_right uu____15619
                            (FStar_List.map
                               (fun u ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u))) in
                        FStar_All.pipe_right uu____15615
                          (FStar_String.concat ", ") in
                      let uu____15675 =
                        let uu____15677 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u ->
                                  let uu____15691 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head in
                                  let uu____15693 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                  FStar_Util.format2 "(%s : %s)" uu____15691
                                    uu____15693)) in
                        FStar_All.pipe_right uu____15677
                          (FStar_String.concat ", ") in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____15613 uu____15675
                    else ());
                   (univs1, uvs, (lbname, e, c1)))) in
           let uu____15714 =
             let uu____15731 = FStar_List.hd lecs in
             univs_and_uvars_of_lec uu____15731 in
           match uu____15714 with
           | (univs, uvs, lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____15821 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1) in
                 if uu____15821
                 then ()
                 else
                   (let uu____15826 = lec_hd in
                    match uu____15826 with
                    | (lb1, uu____15834, uu____15835) ->
                        let uu____15836 = lec2 in
                        (match uu____15836 with
                         | (lb2, uu____15844, uu____15845) ->
                             let msg =
                               let uu____15848 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____15850 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____15848 uu____15850 in
                             let uu____15853 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____15853)) in
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
                 let uu____15921 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1) in
                 if uu____15921
                 then ()
                 else
                   (let uu____15926 = lec_hd in
                    match uu____15926 with
                    | (lb1, uu____15934, uu____15935) ->
                        let uu____15936 = lec2 in
                        (match uu____15936 with
                         | (lb2, uu____15944, uu____15945) ->
                             let msg =
                               let uu____15948 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____15950 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____15948 uu____15950 in
                             let uu____15953 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____15953)) in
               let lecs1 =
                 let uu____15964 = FStar_List.tl lecs in
                 FStar_List.fold_right
                   (fun this_lec ->
                      fun lecs1 ->
                        let uu____16017 = univs_and_uvars_of_lec this_lec in
                        match uu____16017 with
                        | (this_univs, this_uvs, this_lec1) ->
                            (force_univs_eq this_lec1 univs this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____15964 [] in
               let lecs2 = lec_hd :: lecs1 in
               let gen_types uvs1 =
                 let fail rng k =
                   let uu____16127 = lec_hd in
                   match uu____16127 with
                   | (lbname, e, c) ->
                       let uu____16137 =
                         let uu____16143 =
                           let uu____16145 =
                             FStar_Syntax_Print.term_to_string k in
                           let uu____16147 =
                             FStar_Syntax_Print.lbname_to_string lbname in
                           let uu____16149 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c) in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____16145 uu____16147 uu____16149 in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____16143) in
                       FStar_Errors.raise_error uu____16137 rng in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u ->
                         let uu____16171 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head in
                         match uu____16171 with
                         | FStar_Pervasives_Native.Some uu____16180 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____16188 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ in
                             let uu____16192 =
                               FStar_Syntax_Util.arrow_formals k in
                             (match uu____16192 with
                              | (bs, kres) ->
                                  ((let uu____16212 =
                                      let uu____16213 =
                                        let uu____16216 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres in
                                        FStar_Syntax_Util.unrefine
                                          uu____16216 in
                                      uu____16213.FStar_Syntax_Syntax.n in
                                    match uu____16212 with
                                    | FStar_Syntax_Syntax.Tm_type uu____16217
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres in
                                        let uu____16221 =
                                          let uu____16223 =
                                            FStar_Util.set_is_empty free in
                                          Prims.op_Negation uu____16223 in
                                        if uu____16221
                                        then
                                          fail
                                            u.FStar_Syntax_Syntax.ctx_uvar_range
                                            kres
                                        else ()
                                    | uu____16228 ->
                                        fail
                                          u.FStar_Syntax_Syntax.ctx_uvar_range
                                          kres);
                                   (let a =
                                      let uu____16230 =
                                        let uu____16233 =
                                          FStar_TypeChecker_Env.get_range env in
                                        FStar_All.pipe_left
                                          (fun uu____16236 ->
                                             FStar_Pervasives_Native.Some
                                               uu____16236) uu____16233 in
                                      FStar_Syntax_Syntax.new_bv uu____16230
                                        kres in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____16244 ->
                                          let uu____16245 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Util.abs bs
                                            uu____16245
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
                      (fun uu____16348 ->
                         match uu____16348 with
                         | (lbname, e, c) ->
                             let uu____16394 =
                               match (gen_tvars, gen_univs1) with
                               | ([], []) -> (e, c, [])
                               | uu____16455 ->
                                   let uu____16468 = (e, c) in
                                   (match uu____16468 with
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
                                                (fun uu____16508 ->
                                                   match uu____16508 with
                                                   | (x, uu____16514) ->
                                                       let uu____16515 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____16515)
                                                gen_tvars in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____16533 =
                                                let uu____16535 =
                                                  FStar_Util.right lbname in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____16535 in
                                              if uu____16533
                                              then
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  tm tvar_args
                                                  tm.FStar_Syntax_Syntax.pos
                                              else tm in
                                            FStar_Syntax_InstFV.inst
                                              instantiate_lbname_with_app e1
                                          else e1 in
                                        let t =
                                          let uu____16544 =
                                            let uu____16545 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____16545.FStar_Syntax_Syntax.n in
                                          match uu____16544 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs, cod) ->
                                              let uu____16570 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____16570 with
                                               | (bs1, cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____16581 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____16585 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____16585, gen_tvars)) in
                             (match uu____16394 with
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
        (let uu____16732 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____16732
         then
           let uu____16735 =
             let uu____16737 =
               FStar_List.map
                 (fun uu____16752 ->
                    match uu____16752 with
                    | (lb, uu____16761, uu____16762) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_All.pipe_right uu____16737 (FStar_String.concat ", ") in
           FStar_Util.print1 "Generalizing: %s\n" uu____16735
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____16788 ->
                match uu____16788 with
                | (l, t, c) -> gather_free_univnames env t) lecs in
         let generalized_lecs =
           let uu____16817 = gen env is_rec lecs in
           match uu____16817 with
           | FStar_Pervasives_Native.None ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____16916 ->
                       match uu____16916 with
                       | (l, t, c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____16978 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 if uu____16978
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____17026 ->
                           match uu____17026 with
                           | (l, us, e, c, gvs) ->
                               let uu____17060 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos in
                               let uu____17062 =
                                 FStar_Syntax_Print.lbname_to_string l in
                               let uu____17064 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c) in
                               let uu____17066 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____17068 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____17060 uu____17062 uu____17064
                                 uu____17066 uu____17068))
                 else ());
                luecs) in
         FStar_List.map2
           (fun univnames ->
              fun uu____17113 ->
                match uu____17113 with
                | (l, generalized_univs, t, c, gvs) ->
                    let uu____17157 =
                      check_universe_generalization univnames
                        generalized_univs t in
                    (l, uu____17157, t, c, gvs)) univnames_lecs
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
        let uu____17212 =
          let uu____17216 =
            let uu____17218 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.string_of_lid uu____17218 in
          FStar_Pervasives_Native.Some uu____17216 in
        FStar_Profiling.profile
          (fun uu____17235 -> generalize' env is_rec lecs) uu____17212
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
              let uu____17292 =
                FStar_TypeChecker_Rel.get_teq_predicate env2 t1 t21 in
              match uu____17292 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some f ->
                  let uu____17298 = FStar_TypeChecker_Env.apply_guard f e in
                  FStar_All.pipe_right uu____17298
                    (fun uu____17301 ->
                       FStar_Pervasives_Native.Some uu____17301)
            else
              if env2.FStar_TypeChecker_Env.use_eq
              then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
              else
                (let uu____17310 =
                   FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21 in
                 match uu____17310 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some f ->
                     let uu____17316 = FStar_TypeChecker_Env.apply_guard f e in
                     FStar_All.pipe_left
                       (fun uu____17319 ->
                          FStar_Pervasives_Native.Some uu____17319)
                       uu____17316) in
          let uu____17320 = maybe_coerce_lc env1 e lc t2 in
          match uu____17320 with
          | (e1, lc1, g_c) ->
              let uu____17336 =
                check env1 lc1.FStar_TypeChecker_Common.res_typ t2 in
              (match uu____17336 with
               | FStar_Pervasives_Native.None ->
                   let uu____17345 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ in
                   let uu____17351 = FStar_TypeChecker_Env.get_range env1 in
                   FStar_Errors.raise_error uu____17345 uu____17351
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____17360 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____17360
                     then
                       let uu____17365 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____17365
                     else ());
                    (let uu____17371 = FStar_TypeChecker_Env.conj_guard g g_c in
                     (e1, lc1, uu____17371))))
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env ->
    fun g ->
      fun lc ->
        (let uu____17399 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium in
         if uu____17399
         then
           let uu____17402 = FStar_TypeChecker_Common.lcomp_to_string lc in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____17402
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
         let uu____17416 = FStar_TypeChecker_Common.lcomp_comp lc in
         match uu____17416 with
         | (c, g_c) ->
             let uu____17428 = FStar_TypeChecker_Common.is_total_lcomp lc in
             if uu____17428
             then
               let uu____17436 =
                 let uu____17438 = FStar_TypeChecker_Env.conj_guard g1 g_c in
                 discharge uu____17438 in
               (uu____17436, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] in
                let c1 =
                  let uu____17446 =
                    let uu____17447 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    FStar_All.pipe_right uu____17447
                      FStar_Syntax_Syntax.mk_Comp in
                  FStar_All.pipe_right uu____17446
                    (FStar_TypeChecker_Normalize.normalize_comp steps env) in
                let uu____17448 = check_trivial_precondition env c1 in
                match uu____17448 with
                | (ct, vc, g_pre) ->
                    ((let uu____17464 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification") in
                      if uu____17464
                      then
                        let uu____17469 =
                          FStar_Syntax_Print.term_to_string vc in
                        FStar_Util.print1 "top-level VC: %s\n" uu____17469
                      else ());
                     (let uu____17474 =
                        let uu____17476 =
                          let uu____17477 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre in
                          FStar_TypeChecker_Env.conj_guard g1 uu____17477 in
                        discharge uu____17476 in
                      let uu____17478 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp in
                      (uu____17474, uu____17478)))))
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head ->
    fun seen_args ->
      let short_bin_op f uu___8_17512 =
        match uu___8_17512 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst, uu____17522)::[] -> f fst
        | uu____17547 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____17559 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____17559
          (fun uu____17560 -> FStar_TypeChecker_Common.NonTrivial uu____17560) in
      let op_or_e e =
        let uu____17571 =
          let uu____17572 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____17572 in
        FStar_All.pipe_right uu____17571
          (fun uu____17575 -> FStar_TypeChecker_Common.NonTrivial uu____17575) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun uu____17582 -> FStar_TypeChecker_Common.NonTrivial uu____17582) in
      let op_or_t t =
        let uu____17593 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____17593
          (fun uu____17596 -> FStar_TypeChecker_Common.NonTrivial uu____17596) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun uu____17603 -> FStar_TypeChecker_Common.NonTrivial uu____17603) in
      let short_op_ite uu___9_17609 =
        match uu___9_17609 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard, uu____17619)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard, uu____17646)::[] ->
            let uu____17687 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____17687
              (fun uu____17688 ->
                 FStar_TypeChecker_Common.NonTrivial uu____17688)
        | uu____17689 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____17701 =
          let uu____17709 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____17709) in
        let uu____17717 =
          let uu____17727 =
            let uu____17735 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____17735) in
          let uu____17743 =
            let uu____17753 =
              let uu____17761 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____17761) in
            let uu____17769 =
              let uu____17779 =
                let uu____17787 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____17787) in
              let uu____17795 =
                let uu____17805 =
                  let uu____17813 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____17813) in
                [uu____17805; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____17779 :: uu____17795 in
            uu____17753 :: uu____17769 in
          uu____17727 :: uu____17743 in
        uu____17701 :: uu____17717 in
      match head.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____17875 =
            FStar_Util.find_map table
              (fun uu____17890 ->
                 match uu____17890 with
                 | (x, mk) ->
                     let uu____17907 = FStar_Ident.lid_equals x lid in
                     if uu____17907
                     then
                       let uu____17912 = mk seen_args in
                       FStar_Pervasives_Native.Some uu____17912
                     else FStar_Pervasives_Native.None) in
          (match uu____17875 with
           | FStar_Pervasives_Native.None -> FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____17916 -> FStar_TypeChecker_Common.Trivial
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l ->
    let uu____17924 =
      let uu____17925 = FStar_Syntax_Util.un_uinst l in
      uu____17925.FStar_Syntax_Syntax.n in
    match uu____17924 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____17930 -> false
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env ->
    fun bs ->
      let pos bs1 =
        match bs1 with
        | (hd, uu____17966)::uu____17967 ->
            FStar_Syntax_Syntax.range_of_bv hd
        | uu____17986 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____17995, FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____17996))::uu____17997 -> bs
      | uu____18015 ->
          let uu____18016 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____18016 with
           | FStar_Pervasives_Native.None -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____18020 =
                 let uu____18021 = FStar_Syntax_Subst.compress t in
                 uu____18021.FStar_Syntax_Syntax.n in
               (match uu____18020 with
                | FStar_Syntax_Syntax.Tm_arrow (bs', uu____18025) ->
                    let uu____18046 =
                      FStar_Util.prefix_until
                        (fun uu___10_18086 ->
                           match uu___10_18086 with
                           | (uu____18094, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____18095)) ->
                               false
                           | uu____18100 -> true) bs' in
                    (match uu____18046 with
                     | FStar_Pervasives_Native.None -> bs
                     | FStar_Pervasives_Native.Some
                         ([], uu____18136, uu____18137) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps, uu____18209, uu____18210) ->
                         let uu____18283 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____18304 ->
                                   match uu____18304 with
                                   | (x, uu____18313) ->
                                       let uu____18318 =
                                         FStar_Ident.string_of_id
                                           x.FStar_Syntax_Syntax.ppname in
                                       FStar_Util.starts_with uu____18318 "'")) in
                         if uu____18283
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____18364 ->
                                     match uu____18364 with
                                     | (x, i) ->
                                         let uu____18383 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____18383, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____18394 -> bs))
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
            let uu____18423 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1)) in
            if uu____18423
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
          let uu____18454 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____18454
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
        (let uu____18497 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____18497
         then
           ((let uu____18502 = FStar_Ident.string_of_lid lident in
             d uu____18502);
            (let uu____18504 = FStar_Ident.string_of_lid lident in
             let uu____18506 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____18504 uu____18506))
         else ());
        (let fv =
           let uu____18512 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____18512
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
         let uu____18524 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Range.dummyRange in
         ((let uu___2115_18526 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2115_18526.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2115_18526.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2115_18526.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2115_18526.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2115_18526.FStar_Syntax_Syntax.sigopts)
           }), uu____18524))
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env ->
    fun se ->
      let visibility uu___11_18544 =
        match uu___11_18544 with
        | FStar_Syntax_Syntax.Private -> true
        | uu____18547 -> false in
      let reducibility uu___12_18555 =
        match uu___12_18555 with
        | FStar_Syntax_Syntax.Abstract -> true
        | FStar_Syntax_Syntax.Irreducible -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> true
        | FStar_Syntax_Syntax.Visible_default -> true
        | FStar_Syntax_Syntax.Inline_for_extraction -> true
        | uu____18562 -> false in
      let assumption uu___13_18570 =
        match uu___13_18570 with
        | FStar_Syntax_Syntax.Assumption -> true
        | FStar_Syntax_Syntax.New -> true
        | uu____18574 -> false in
      let reification uu___14_18582 =
        match uu___14_18582 with
        | FStar_Syntax_Syntax.Reifiable -> true
        | FStar_Syntax_Syntax.Reflectable uu____18585 -> true
        | uu____18587 -> false in
      let inferred uu___15_18595 =
        match uu___15_18595 with
        | FStar_Syntax_Syntax.Discriminator uu____18597 -> true
        | FStar_Syntax_Syntax.Projector uu____18599 -> true
        | FStar_Syntax_Syntax.RecordType uu____18605 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____18615 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor -> true
        | FStar_Syntax_Syntax.HasMaskedEffect -> true
        | FStar_Syntax_Syntax.Effect -> true
        | uu____18628 -> false in
      let has_eq uu___16_18636 =
        match uu___16_18636 with
        | FStar_Syntax_Syntax.Noeq -> true
        | FStar_Syntax_Syntax.Unopteq -> true
        | uu____18640 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____18719 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private -> true
        | uu____18726 -> true in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1 in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l ->
                  let uu____18759 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l in
                  FStar_Option.isSome uu____18759)) in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____18790 = FStar_Option.get attrs_opt in
                     FStar_Syntax_Util.has_attribute uu____18790
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
           | FStar_Syntax_Syntax.Sig_bundle uu____18810 ->
               let uu____18819 =
                 let uu____18821 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_18827 ->
                           match uu___17_18827 with
                           | FStar_Syntax_Syntax.Noeq -> true
                           | uu____18830 -> false)) in
                 Prims.op_Negation uu____18821 in
               if uu____18819
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____18837 -> ()
           | FStar_Syntax_Syntax.Sig_fail uu____18844 -> ()
           | uu____18857 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_QulifierListNotPermitted,
                   "Illegal attribute: the `erasable` attribute is only permitted on inductive type definitions")
                 r)
        else () in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic))) in
      let uu____18871 =
        let uu____18873 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_18879 ->
                  match uu___18_18879 with
                  | FStar_Syntax_Syntax.OnlyName -> true
                  | uu____18882 -> false)) in
        FStar_All.pipe_right uu____18873 Prims.op_Negation in
      if uu____18871
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x -> fun y -> x = y) quals in
        let err' msg =
          let uu____18903 =
            let uu____18909 =
              let uu____18911 = FStar_Syntax_Print.quals_to_string quals in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____18911 msg in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____18909) in
          FStar_Errors.raise_error uu____18903 r in
        let err msg = err' (Prims.op_Hat ": " msg) in
        let err'1 uu____18929 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____18937 =
            let uu____18939 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____18939 in
          if uu____18937 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec, uu____18950), uu____18951)
              ->
              ((let uu____18963 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____18963
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____18972 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x -> (assumption x) || (has_eq x))) in
                if uu____18972
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____18983 ->
              ((let uu____18993 =
                  let uu____18995 =
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
                  Prims.op_Negation uu____18995 in
                if uu____18993 then err'1 () else ());
               (let uu____19005 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_19011 ->
                           match uu___19_19011 with
                           | FStar_Syntax_Syntax.Unopteq -> true
                           | uu____19014 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr) in
                if uu____19005
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____19020 ->
              let uu____19027 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____19027 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____19035 ->
              let uu____19042 =
                let uu____19044 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____19044 in
              if uu____19042 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____19054 ->
              let uu____19055 =
                let uu____19057 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____19057 in
              if uu____19055 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19067 ->
              let uu____19080 =
                let uu____19082 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____19082 in
              if uu____19080 then err'1 () else ()
          | uu____19092 -> ()))
      else ()
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g ->
    fun t ->
      let rec descend env t1 =
        let uu____19131 =
          let uu____19132 = FStar_Syntax_Subst.compress t1 in
          uu____19132.FStar_Syntax_Syntax.n in
        match uu____19131 with
        | FStar_Syntax_Syntax.Tm_arrow uu____19136 ->
            let uu____19151 = FStar_Syntax_Util.arrow_formals_comp t1 in
            (match uu____19151 with
             | (bs, c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____19160;
               FStar_Syntax_Syntax.index = uu____19161;
               FStar_Syntax_Syntax.sort = t2;_},
             uu____19163)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head, uu____19172) -> descend env head
        | FStar_Syntax_Syntax.Tm_uinst (head, uu____19198) ->
            descend env head
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____19204 -> false
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
        (let uu____19214 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction") in
         if uu____19214
         then
           let uu____19219 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____19219
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
                  let uu____19284 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t in
                  FStar_Errors.raise_error uu____19284 r in
                let uu____19294 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts in
                match uu____19294 with
                | (uu____19303, signature) ->
                    let uu____19305 =
                      let uu____19306 = FStar_Syntax_Subst.compress signature in
                      uu____19306.FStar_Syntax_Syntax.n in
                    (match uu____19305 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs, uu____19314) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____19362 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b ->
                                     let uu____19378 =
                                       FStar_Syntax_Print.binder_to_string b in
                                     let uu____19380 =
                                       FStar_Ident.string_of_lid eff_name in
                                     let uu____19382 =
                                       FStar_Range.string_of_range r in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____19378 uu____19380 uu____19382) r in
                              (match uu____19362 with
                               | (is, g) ->
                                   let uu____19395 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None ->
                                         let eff_c =
                                           let uu____19397 =
                                             let uu____19398 =
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
                                                 = uu____19398;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____19397 in
                                         let uu____19417 =
                                           let uu____19418 =
                                             let uu____19433 =
                                               let uu____19442 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   FStar_Syntax_Syntax.t_unit in
                                               [uu____19442] in
                                             (uu____19433, eff_c) in
                                           FStar_Syntax_Syntax.Tm_arrow
                                             uu____19418 in
                                         FStar_Syntax_Syntax.mk uu____19417 r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____19473 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u] in
                                           FStar_All.pipe_right uu____19473
                                             FStar_Pervasives_Native.snd in
                                         let uu____19482 =
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg (a_tm
                                             :: is) in
                                         FStar_Syntax_Syntax.mk_Tm_app repr
                                           uu____19482 r in
                                   (uu____19395, g))
                          | uu____19491 -> fail signature)
                     | uu____19492 -> fail signature)
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
            let uu____19523 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env) in
            FStar_All.pipe_right uu____19523
              (fun ed ->
                 let uu____19531 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____19531 u a_tm)
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
              let uu____19567 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u] in
              match uu____19567 with
              | (uu____19572, sig_tm) ->
                  let fail t =
                    let uu____19580 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t in
                    FStar_Errors.raise_error uu____19580 r in
                  let uu____19586 =
                    let uu____19587 = FStar_Syntax_Subst.compress sig_tm in
                    uu____19587.FStar_Syntax_Syntax.n in
                  (match uu____19586 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs, uu____19591) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs in
                       (match bs1 with
                        | (a', uu____19614)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____19636 -> fail sig_tm)
                   | uu____19637 -> fail sig_tm)
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
          (let uu____19668 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects") in
           if uu____19668
           then
             let uu____19673 = FStar_Syntax_Print.comp_to_string c in
             let uu____19675 = FStar_Syntax_Print.lid_to_string tgt in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____19673 uu____19675
           else ());
          (let r = FStar_TypeChecker_Env.get_range env in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c in
           let lift_name =
             let uu____19684 =
               FStar_Ident.string_of_lid ct.FStar_Syntax_Syntax.effect_name in
             let uu____19686 = FStar_Ident.string_of_lid tgt in
             FStar_Util.format2 "%s ~> %s" uu____19684 uu____19686 in
           let uu____19689 =
             let uu____19700 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs in
             let uu____19701 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst) in
             (uu____19700, (ct.FStar_Syntax_Syntax.result_typ), uu____19701) in
           match uu____19689 with
           | (u, a, c_is) ->
               let uu____19749 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u] in
               (match uu____19749 with
                | (uu____19758, lift_t) ->
                    let lift_t_shape_error s =
                      let uu____19769 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name in
                      let uu____19771 = FStar_Ident.string_of_lid tgt in
                      let uu____19773 =
                        FStar_Syntax_Print.term_to_string lift_t in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____19769 uu____19771 s uu____19773 in
                    let uu____19776 =
                      let uu____19809 =
                        let uu____19810 = FStar_Syntax_Subst.compress lift_t in
                        uu____19810.FStar_Syntax_Syntax.n in
                      match uu____19809 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs, c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____19874 =
                            FStar_Syntax_Subst.open_comp bs c1 in
                          (match uu____19874 with
                           | (a_b::bs1, c2) ->
                               let uu____19934 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one)) in
                               (a_b, uu____19934, c2))
                      | uu____20022 ->
                          let uu____20023 =
                            let uu____20029 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders" in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____20029) in
                          FStar_Errors.raise_error uu____20023 r in
                    (match uu____19776 with
                     | (a_b, (rest_bs, f_b::[]), lift_c) ->
                         let uu____20147 =
                           let uu____20154 =
                             let uu____20155 =
                               let uu____20156 =
                                 let uu____20163 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst in
                                 (uu____20163, a) in
                               FStar_Syntax_Syntax.NT uu____20156 in
                             [uu____20155] in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____20154
                             (fun b ->
                                let uu____20180 =
                                  FStar_Syntax_Print.binder_to_string b in
                                let uu____20182 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name in
                                let uu____20184 =
                                  FStar_Ident.string_of_lid tgt in
                                let uu____20186 =
                                  FStar_Range.string_of_range r in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____20180 uu____20182 uu____20184
                                  uu____20186) r in
                         (match uu____20147 with
                          | (rest_bs_uvars, g) ->
                              ((let uu____20200 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects") in
                                if uu____20200
                                then
                                  let uu____20205 =
                                    FStar_List.fold_left
                                      (fun s ->
                                         fun u1 ->
                                           let uu____20214 =
                                             let uu____20216 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1 in
                                             Prims.op_Hat ";;;;" uu____20216 in
                                           Prims.op_Hat s uu____20214) ""
                                      rest_bs_uvars in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____20205
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b ->
                                       fun t ->
                                         let uu____20247 =
                                           let uu____20254 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst in
                                           (uu____20254, t) in
                                         FStar_Syntax_Syntax.NT uu____20247)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars) in
                                let guard_f =
                                  let f_sort =
                                    let uu____20273 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs) in
                                    FStar_All.pipe_right uu____20273
                                      FStar_Syntax_Subst.compress in
                                  let f_sort_is =
                                    let uu____20279 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name in
                                    effect_args_from_repr f_sort uu____20279
                                      r in
                                  FStar_List.fold_left2
                                    (fun g1 ->
                                       fun i1 ->
                                         fun i2 ->
                                           let uu____20288 =
                                             FStar_TypeChecker_Rel.layered_effect_teq
                                               env i1 i2
                                               (FStar_Pervasives_Native.Some
                                                  lift_name) in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____20288)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is in
                                let lift_ct =
                                  let uu____20291 =
                                    FStar_All.pipe_right lift_c
                                      (FStar_Syntax_Subst.subst_comp substs) in
                                  FStar_All.pipe_right uu____20291
                                    FStar_Syntax_Util.comp_to_comp_typ in
                                let is =
                                  let uu____20295 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____20295 r in
                                let fml =
                                  let uu____20300 =
                                    let uu____20305 =
                                      FStar_List.hd
                                        lift_ct.FStar_Syntax_Syntax.comp_univs in
                                    let uu____20306 =
                                      let uu____20307 =
                                        FStar_List.hd
                                          lift_ct.FStar_Syntax_Syntax.effect_args in
                                      FStar_Pervasives_Native.fst uu____20307 in
                                    (uu____20305, uu____20306) in
                                  match uu____20300 with
                                  | (u1, wp) ->
                                      FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                        env u1
                                        lift_ct.FStar_Syntax_Syntax.result_typ
                                        wp FStar_Range.dummyRange in
                                (let uu____20333 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects"))
                                     &&
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme) in
                                 if uu____20333
                                 then
                                   let uu____20339 =
                                     FStar_Syntax_Print.term_to_string fml in
                                   FStar_Util.print1 "Guard for lift is: %s"
                                     uu____20339
                                 else ());
                                (let c1 =
                                   let uu____20345 =
                                     let uu____20346 =
                                       FStar_All.pipe_right is
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.as_arg) in
                                     {
                                       FStar_Syntax_Syntax.comp_univs =
                                         (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                       FStar_Syntax_Syntax.effect_name = tgt;
                                       FStar_Syntax_Syntax.result_typ = a;
                                       FStar_Syntax_Syntax.effect_args =
                                         uu____20346;
                                       FStar_Syntax_Syntax.flags = []
                                     } in
                                   FStar_Syntax_Syntax.mk_Comp uu____20345 in
                                 (let uu____20370 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects") in
                                  if uu____20370
                                  then
                                    let uu____20375 =
                                      FStar_Syntax_Print.comp_to_string c1 in
                                    FStar_Util.print1 "} Lifted comp: %s\n"
                                      uu____20375
                                  else ());
                                 (let uu____20380 =
                                    let uu____20381 =
                                      FStar_TypeChecker_Env.conj_guard g
                                        guard_f in
                                    let uu____20382 =
                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                        (FStar_TypeChecker_Common.NonTrivial
                                           fml) in
                                    FStar_TypeChecker_Env.conj_guard
                                      uu____20381 uu____20382 in
                                  (c1, uu____20380)))))))))
let lift_tf_layered_effect_term :
  'uuuuuu20396 .
    'uuuuuu20396 ->
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
              let uu____20425 =
                let uu____20430 =
                  FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift
                    FStar_Util.must in
                FStar_All.pipe_right uu____20430
                  (fun ts -> FStar_TypeChecker_Env.inst_tscheme_with ts [u]) in
              FStar_All.pipe_right uu____20425 FStar_Pervasives_Native.snd in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must in
              let uu____20473 =
                let uu____20474 =
                  let uu____20477 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd in
                  FStar_All.pipe_right uu____20477
                    FStar_Syntax_Subst.compress in
                uu____20474.FStar_Syntax_Syntax.n in
              match uu____20473 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____20500::bs, uu____20502)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____20542 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one)) in
                  FStar_All.pipe_right uu____20542
                    FStar_Pervasives_Native.fst
              | uu____20648 ->
                  let uu____20649 =
                    let uu____20655 =
                      let uu____20657 =
                        FStar_Syntax_Print.tscheme_to_string lift_t in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____20657 in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____20655) in
                  FStar_Errors.raise_error uu____20649
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos in
            let args =
              let uu____20684 = FStar_Syntax_Syntax.as_arg a in
              let uu____20693 =
                let uu____20704 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____20740 ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const)) in
                let uu____20747 =
                  let uu____20758 = FStar_Syntax_Syntax.as_arg e in
                  [uu____20758] in
                FStar_List.append uu____20704 uu____20747 in
              uu____20684 :: uu____20693 in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              e.FStar_Syntax_Syntax.pos
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env ->
    fun datacon ->
      fun index ->
        let uu____20829 = FStar_TypeChecker_Env.lookup_datacon env datacon in
        match uu____20829 with
        | (uu____20834, t) ->
            let err n =
              let uu____20844 =
                let uu____20850 =
                  let uu____20852 = FStar_Ident.string_of_lid datacon in
                  let uu____20854 = FStar_Util.string_of_int n in
                  let uu____20856 = FStar_Util.string_of_int index in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____20852 uu____20854 uu____20856 in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____20850) in
              let uu____20860 = FStar_TypeChecker_Env.get_range env in
              FStar_Errors.raise_error uu____20844 uu____20860 in
            let uu____20861 =
              let uu____20862 = FStar_Syntax_Subst.compress t in
              uu____20862.FStar_Syntax_Syntax.n in
            (match uu____20861 with
             | FStar_Syntax_Syntax.Tm_arrow (bs, uu____20866) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____20921 ->
                           match uu____20921 with
                           | (uu____20929, q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true)) ->
                                    false
                                | uu____20938 -> true))) in
                 if (FStar_List.length bs1) <= index
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index in
                    FStar_Syntax_Util.mk_field_projector_name datacon
                      (FStar_Pervasives_Native.fst b) index)
             | uu____20972 -> err Prims.int_zero)
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env ->
    fun sub ->
      let uu____20985 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub.FStar_Syntax_Syntax.target) in
      if uu____20985
      then
        let uu____20988 =
          let uu____21001 =
            FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must in
          lift_tf_layered_effect sub.FStar_Syntax_Syntax.target uu____21001 in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____20988;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c in
           let uu____21036 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs in
           match uu____21036 with
           | (uu____21045, lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args in
               let uu____21064 =
                 let uu____21065 =
                   let uu___2492_21066 = ct in
                   let uu____21067 =
                     let uu____21078 =
                       let uu____21087 =
                         let uu____21088 =
                           let uu____21089 =
                             let uu____21106 =
                               let uu____21117 =
                                 FStar_Syntax_Syntax.as_arg
                                   ct.FStar_Syntax_Syntax.result_typ in
                               [uu____21117; wp] in
                             (lift_t, uu____21106) in
                           FStar_Syntax_Syntax.Tm_app uu____21089 in
                         FStar_Syntax_Syntax.mk uu____21088
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos in
                       FStar_All.pipe_right uu____21087
                         FStar_Syntax_Syntax.as_arg in
                     [uu____21078] in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2492_21066.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2492_21066.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____21067;
                     FStar_Syntax_Syntax.flags =
                       (uu___2492_21066.FStar_Syntax_Syntax.flags)
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____21065 in
               (uu____21064, FStar_TypeChecker_Common.trivial_guard) in
         let mk_mlift_term ts u r e =
           let uu____21217 = FStar_TypeChecker_Env.inst_tscheme_with ts [u] in
           match uu____21217 with
           | (uu____21224, lift_t) ->
               let uu____21226 =
                 let uu____21227 =
                   let uu____21244 =
                     let uu____21255 = FStar_Syntax_Syntax.as_arg r in
                     let uu____21264 =
                       let uu____21275 =
                         FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun in
                       let uu____21284 =
                         let uu____21295 = FStar_Syntax_Syntax.as_arg e in
                         [uu____21295] in
                       uu____21275 :: uu____21284 in
                     uu____21255 :: uu____21264 in
                   (lift_t, uu____21244) in
                 FStar_Syntax_Syntax.Tm_app uu____21227 in
               FStar_Syntax_Syntax.mk uu____21226 e.FStar_Syntax_Syntax.pos in
         let uu____21348 =
           let uu____21361 =
             FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must in
           FStar_All.pipe_right uu____21361 mk_mlift_wp in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____21348;
           FStar_TypeChecker_Env.mlift_term =
             (match sub.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____21397 ->
                        fun uu____21398 -> fun e -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env ->
    fun sub ->
      let uu____21421 = get_mlift_for_subeff env sub in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub.FStar_Syntax_Syntax.source sub.FStar_Syntax_Syntax.target
        uu____21421
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