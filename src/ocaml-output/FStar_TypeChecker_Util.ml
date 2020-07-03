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
let (is_ghost_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun l ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l in
      FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid
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
          let uu____2546 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid in
          if uu____2546
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____2558 =
      let uu____2559 = FStar_Syntax_Subst.compress t in
      uu____2559.FStar_Syntax_Syntax.n in
    match uu____2558 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2563 -> true
    | uu____2579 -> false
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
              let uu____2649 =
                let uu____2651 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____2651 in
              if uu____2649
              then f
              else (let uu____2658 = reason1 () in label uu____2658 r f)
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
            let uu___354_2679 = g in
            let uu____2680 =
              let uu____2681 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____2681 in
            {
              FStar_TypeChecker_Common.guard_f = uu____2680;
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___354_2679.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___354_2679.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___354_2679.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___354_2679.FStar_TypeChecker_Common.implicits)
            }
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun bvs ->
      fun c ->
        let uu____2702 = FStar_Syntax_Util.is_ml_comp c in
        if uu____2702
        then c
        else
          (let uu____2707 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____2707
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close =
                  let uu____2749 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator in
                  FStar_All.pipe_right uu____2749 FStar_Util.must in
                FStar_List.fold_right
                  (fun x ->
                     fun wp ->
                       let bs =
                         let uu____2778 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____2778] in
                       let us =
                         let uu____2800 =
                           let uu____2803 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____2803] in
                         u_res :: uu____2800 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu____2809 =
                         FStar_TypeChecker_Env.inst_effect_fun_with us env md
                           close in
                       let uu____2810 =
                         let uu____2811 = FStar_Syntax_Syntax.as_arg res_t in
                         let uu____2820 =
                           let uu____2831 =
                             FStar_Syntax_Syntax.as_arg
                               x.FStar_Syntax_Syntax.sort in
                           let uu____2840 =
                             let uu____2851 = FStar_Syntax_Syntax.as_arg wp1 in
                             [uu____2851] in
                           uu____2831 :: uu____2840 in
                         uu____2811 :: uu____2820 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____2809 uu____2810
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____2893 = destruct_wp_comp c1 in
              match uu____2893 with
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
                let uu____2933 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs) in
                FStar_All.pipe_right uu____2933
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
                  let uu____2983 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs) in
                  FStar_All.pipe_right uu____2983
                    (close_guard_implicits env false bs)))
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_2996 ->
            match uu___0_2996 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> true
            | uu____2999 -> false))
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env ->
    fun eopt ->
      fun lc ->
        let lc_is_unit_or_effectful =
          let uu____3024 =
            let uu____3027 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp in
            FStar_All.pipe_right uu____3027 FStar_Pervasives_Native.snd in
          FStar_All.pipe_right uu____3024
            (fun c ->
               (let uu____3051 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c in
                Prims.op_Negation uu____3051) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____3055 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c in
                     Prims.op_Negation uu____3055))) in
        match eopt with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____3066 = FStar_Syntax_Util.head_and_args' e in
                match uu____3066 with
                | (head, uu____3083) ->
                    let uu____3104 =
                      let uu____3105 = FStar_Syntax_Util.un_uinst head in
                      uu____3105.FStar_Syntax_Syntax.n in
                    (match uu____3104 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____3110 =
                           let uu____3112 = FStar_Syntax_Syntax.lid_of_fv fv in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____3112 in
                         Prims.op_Negation uu____3110
                     | uu____3113 -> true)))
              &&
              (let uu____3116 = should_not_inline_lc lc in
               Prims.op_Negation uu____3116)
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
            let uu____3162 =
              FStar_TypeChecker_Env.get_effect_decl env eff_lid in
            mk_return env uu____3162 u t v v.FStar_Syntax_Syntax.pos
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
                        let uu____3232 =
                          let uu____3234 =
                            FStar_All.pipe_right m FStar_Ident.ident_of_lid in
                          FStar_All.pipe_right uu____3234
                            FStar_Ident.string_of_id in
                        let uu____3236 =
                          let uu____3238 =
                            FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                          FStar_All.pipe_right uu____3238
                            FStar_Ident.string_of_id in
                        let uu____3240 =
                          let uu____3242 =
                            FStar_All.pipe_right p FStar_Ident.ident_of_lid in
                          FStar_All.pipe_right uu____3242
                            FStar_Ident.string_of_id in
                        FStar_Util.format3 "(%s, %s) |> %s" uu____3232
                          uu____3236 uu____3240 in
                      (let uu____3246 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LayeredEffects") in
                       if uu____3246
                       then
                         let uu____3251 =
                           let uu____3253 = FStar_Syntax_Syntax.mk_Comp ct1 in
                           FStar_Syntax_Print.comp_to_string uu____3253 in
                         let uu____3254 =
                           let uu____3256 = FStar_Syntax_Syntax.mk_Comp ct2 in
                           FStar_Syntax_Print.comp_to_string uu____3256 in
                         FStar_Util.print2 "Binding c1:%s and c2:%s {\n"
                           uu____3251 uu____3254
                       else ());
                      (let uu____3261 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "ResolveImplicitsHook") in
                       if uu____3261
                       then
                         let uu____3266 =
                           let uu____3268 =
                             FStar_TypeChecker_Env.get_range env in
                           FStar_Range.string_of_range uu____3268 in
                         let uu____3269 =
                           FStar_Syntax_Print.tscheme_to_string bind_t in
                         FStar_Util.print2
                           "///////////////////////////////Bind at %s/////////////////////\nwith bind_t = %s\n"
                           uu____3266 uu____3269
                       else ());
                      (let uu____3274 =
                         let uu____3281 =
                           FStar_TypeChecker_Env.get_effect_decl env m in
                         let uu____3282 =
                           FStar_TypeChecker_Env.get_effect_decl env n in
                         let uu____3283 =
                           FStar_TypeChecker_Env.get_effect_decl env p in
                         (uu____3281, uu____3282, uu____3283) in
                       match uu____3274 with
                       | (m_ed, n_ed, p_ed) ->
                           let uu____3291 =
                             let uu____3304 =
                               FStar_List.hd
                                 ct1.FStar_Syntax_Syntax.comp_univs in
                             let uu____3305 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 ct1.FStar_Syntax_Syntax.effect_args in
                             (uu____3304,
                               (ct1.FStar_Syntax_Syntax.result_typ),
                               uu____3305) in
                           (match uu____3291 with
                            | (u1, t1, is1) ->
                                let uu____3349 =
                                  let uu____3362 =
                                    FStar_List.hd
                                      ct2.FStar_Syntax_Syntax.comp_univs in
                                  let uu____3363 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst
                                      ct2.FStar_Syntax_Syntax.effect_args in
                                  (uu____3362,
                                    (ct2.FStar_Syntax_Syntax.result_typ),
                                    uu____3363) in
                                (match uu____3349 with
                                 | (u2, t2, is2) ->
                                     let uu____3407 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         bind_t [u1; u2] in
                                     (match uu____3407 with
                                      | (uu____3416, bind_t1) ->
                                          let bind_t_shape_error s =
                                            let uu____3431 =
                                              let uu____3433 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t1 in
                                              FStar_Util.format3
                                                "bind %s (%s) does not have proper shape (reason:%s)"
                                                uu____3433 bind_name s in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu____3431) in
                                          let uu____3437 =
                                            let uu____3482 =
                                              let uu____3483 =
                                                FStar_Syntax_Subst.compress
                                                  bind_t1 in
                                              uu____3483.FStar_Syntax_Syntax.n in
                                            match uu____3482 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs, c) when
                                                (FStar_List.length bs) >=
                                                  (Prims.of_int (4))
                                                ->
                                                let uu____3559 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs c in
                                                (match uu____3559 with
                                                 | (a_b::b_b::bs1, c1) ->
                                                     let uu____3644 =
                                                       let uu____3671 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2)))
                                                           bs1 in
                                                       FStar_All.pipe_right
                                                         uu____3671
                                                         (fun uu____3756 ->
                                                            match uu____3756
                                                            with
                                                            | (l1, l2) ->
                                                                let uu____3837
                                                                  =
                                                                  FStar_List.hd
                                                                    l2 in
                                                                let uu____3850
                                                                  =
                                                                  let uu____3857
                                                                    =
                                                                    FStar_List.tl
                                                                    l2 in
                                                                  FStar_List.hd
                                                                    uu____3857 in
                                                                (l1,
                                                                  uu____3837,
                                                                  uu____3850)) in
                                                     (match uu____3644 with
                                                      | (rest_bs, f_b, g_b)
                                                          ->
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b, c1)))
                                            | uu____4017 ->
                                                let uu____4018 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders" in
                                                FStar_Errors.raise_error
                                                  uu____4018 r1 in
                                          (match uu____3437 with
                                           | (a_b, b_b, rest_bs, f_b, g_b,
                                              bind_c) ->
                                               let uu____4143 =
                                                 let uu____4150 =
                                                   let uu____4151 =
                                                     let uu____4152 =
                                                       let uu____4159 =
                                                         FStar_All.pipe_right
                                                           a_b
                                                           FStar_Pervasives_Native.fst in
                                                       (uu____4159, t1) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____4152 in
                                                   let uu____4170 =
                                                     let uu____4173 =
                                                       let uu____4174 =
                                                         let uu____4181 =
                                                           FStar_All.pipe_right
                                                             b_b
                                                             FStar_Pervasives_Native.fst in
                                                         (uu____4181, t2) in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____4174 in
                                                     [uu____4173] in
                                                   uu____4151 :: uu____4170 in
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs uu____4150
                                                   (fun b1 ->
                                                      let uu____4196 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1 in
                                                      let uu____4198 =
                                                        FStar_Range.string_of_range
                                                          r1 in
                                                      FStar_Util.format3
                                                        "implicit var for binder %s of %s at %s"
                                                        uu____4196 bind_name
                                                        uu____4198) r1 in
                                               (match uu____4143 with
                                                | (rest_bs_uvars, g_uvars) ->
                                                    ((let uu____4212 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "ResolveImplicitsHook") in
                                                      if uu____4212
                                                      then
                                                        FStar_All.pipe_right
                                                          rest_bs_uvars
                                                          (FStar_List.iter
                                                             (fun t ->
                                                                let uu____4226
                                                                  =
                                                                  let uu____4227
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    t in
                                                                  uu____4227.FStar_Syntax_Syntax.n in
                                                                match uu____4226
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (u,
                                                                    uu____4231)
                                                                    ->
                                                                    let uu____4248
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t in
                                                                    let uu____4250
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
                                                                    uu____4256
                                                                    ->
                                                                    "<no attr>" in
                                                                    FStar_Util.print2
                                                                    "Generated uvar %s with attribute %s\n"
                                                                    uu____4248
                                                                    uu____4250))
                                                      else ());
                                                     (let subst =
                                                        FStar_List.map2
                                                          (fun b1 ->
                                                             fun t ->
                                                               let uu____4287
                                                                 =
                                                                 let uu____4294
                                                                   =
                                                                   FStar_All.pipe_right
                                                                    b1
                                                                    FStar_Pervasives_Native.fst in
                                                                 (uu____4294,
                                                                   t) in
                                                               FStar_Syntax_Syntax.NT
                                                                 uu____4287)
                                                          (a_b :: b_b ::
                                                          rest_bs) (t1 :: t2
                                                          :: rest_bs_uvars) in
                                                      let f_guard =
                                                        let f_sort_is =
                                                          let uu____4323 =
                                                            let uu____4326 =
                                                              let uu____4327
                                                                =
                                                                let uu____4328
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    f_b
                                                                    FStar_Pervasives_Native.fst in
                                                                uu____4328.FStar_Syntax_Syntax.sort in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4327 in
                                                            let uu____4337 =
                                                              FStar_Syntax_Util.is_layered
                                                                m_ed in
                                                            effect_args_from_repr
                                                              uu____4326
                                                              uu____4337 r1 in
                                                          FStar_All.pipe_right
                                                            uu____4323
                                                            (FStar_List.map
                                                               (FStar_Syntax_Subst.subst
                                                                  subst)) in
                                                        FStar_List.fold_left2
                                                          (fun g ->
                                                             fun i1 ->
                                                               fun f_i1 ->
                                                                 (let uu____4362
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "ResolveImplicitsHook") in
                                                                  if
                                                                    uu____4362
                                                                  then
                                                                    let uu____4367
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    i1 in
                                                                    let uu____4369
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    f_i1 in
                                                                    FStar_Util.print2
                                                                    "Generating constraint %s = %s\n"
                                                                    uu____4367
                                                                    uu____4369
                                                                  else ());
                                                                 (let uu____4374
                                                                    =
                                                                    FStar_TypeChecker_Rel.layered_effect_teq
                                                                    env i1
                                                                    f_i1
                                                                    (FStar_Pervasives_Native.Some
                                                                    bind_name) in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____4374))
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
                                                          let uu____4394 =
                                                            let uu____4395 =
                                                              let uu____4398
                                                                =
                                                                let uu____4399
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    g_b
                                                                    FStar_Pervasives_Native.fst in
                                                                uu____4399.FStar_Syntax_Syntax.sort in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4398 in
                                                            uu____4395.FStar_Syntax_Syntax.n in
                                                          match uu____4394
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_arrow
                                                              (bs, c) ->
                                                              let uu____4432
                                                                =
                                                                FStar_Syntax_Subst.open_comp
                                                                  bs c in
                                                              (match uu____4432
                                                               with
                                                               | (bs1, c1) ->
                                                                   let bs_subst
                                                                    =
                                                                    let uu____4442
                                                                    =
                                                                    let uu____4449
                                                                    =
                                                                    let uu____4450
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1 in
                                                                    FStar_All.pipe_right
                                                                    uu____4450
                                                                    FStar_Pervasives_Native.fst in
                                                                    let uu____4471
                                                                    =
                                                                    let uu____4474
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst in
                                                                    FStar_All.pipe_right
                                                                    uu____4474
                                                                    FStar_Syntax_Syntax.bv_to_name in
                                                                    (uu____4449,
                                                                    uu____4471) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4442 in
                                                                   let c2 =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1 in
                                                                   let uu____4488
                                                                    =
                                                                    let uu____4491
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2) in
                                                                    let uu____4492
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed in
                                                                    effect_args_from_repr
                                                                    uu____4491
                                                                    uu____4492
                                                                    r1 in
                                                                   FStar_All.pipe_right
                                                                    uu____4488
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst)))
                                                          | uu____4498 ->
                                                              failwith
                                                                "impossible: mk_indexed_bind" in
                                                        let env_g =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env [x_a] in
                                                        let uu____4515 =
                                                          FStar_List.fold_left2
                                                            (fun g ->
                                                               fun i1 ->
                                                                 fun g_i1 ->
                                                                   (let uu____4533
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "ResolveImplicitsHook") in
                                                                    if
                                                                    uu____4533
                                                                    then
                                                                    let uu____4538
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    i1 in
                                                                    let uu____4540
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    g_i1 in
                                                                    FStar_Util.print2
                                                                    "Generating constraint %s = %s\n"
                                                                    uu____4538
                                                                    uu____4540
                                                                    else ());
                                                                   (let uu____4545
                                                                    =
                                                                    FStar_TypeChecker_Rel.layered_effect_teq
                                                                    env_g i1
                                                                    g_i1
                                                                    (FStar_Pervasives_Native.Some
                                                                    bind_name) in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____4545))
                                                            FStar_TypeChecker_Env.trivial_guard
                                                            is2 g_sort_is in
                                                        FStar_All.pipe_right
                                                          uu____4515
                                                          (FStar_TypeChecker_Env.close_guard
                                                             env [x_a]) in
                                                      let bind_ct =
                                                        let uu____4560 =
                                                          FStar_All.pipe_right
                                                            bind_c
                                                            (FStar_Syntax_Subst.subst_comp
                                                               subst) in
                                                        FStar_All.pipe_right
                                                          uu____4560
                                                          FStar_Syntax_Util.comp_to_comp_typ in
                                                      let fml =
                                                        let uu____4562 =
                                                          let uu____4567 =
                                                            FStar_List.hd
                                                              bind_ct.FStar_Syntax_Syntax.comp_univs in
                                                          let uu____4568 =
                                                            let uu____4569 =
                                                              FStar_List.hd
                                                                bind_ct.FStar_Syntax_Syntax.effect_args in
                                                            FStar_Pervasives_Native.fst
                                                              uu____4569 in
                                                          (uu____4567,
                                                            uu____4568) in
                                                        match uu____4562 with
                                                        | (u, wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              bind_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange in
                                                      let is =
                                                        let uu____4595 =
                                                          FStar_Syntax_Subst.compress
                                                            bind_ct.FStar_Syntax_Syntax.result_typ in
                                                        let uu____4596 =
                                                          FStar_Syntax_Util.is_layered
                                                            p_ed in
                                                        effect_args_from_repr
                                                          uu____4595
                                                          uu____4596 r1 in
                                                      let c =
                                                        let uu____4599 =
                                                          let uu____4600 =
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
                                                              = uu____4600;
                                                            FStar_Syntax_Syntax.flags
                                                              = flags
                                                          } in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____4599 in
                                                      (let uu____4620 =
                                                         FStar_All.pipe_left
                                                           (FStar_TypeChecker_Env.debug
                                                              env)
                                                           (FStar_Options.Other
                                                              "LayeredEffects") in
                                                       if uu____4620
                                                       then
                                                         let uu____4625 =
                                                           FStar_Syntax_Print.comp_to_string
                                                             c in
                                                         FStar_Util.print1
                                                           "} c after bind: %s\n"
                                                           uu____4625
                                                       else ());
                                                      (let guard =
                                                         let uu____4631 =
                                                           let uu____4634 =
                                                             let uu____4637 =
                                                               let uu____4640
                                                                 =
                                                                 let uu____4643
                                                                   =
                                                                   FStar_TypeChecker_Env.guard_of_guard_formula
                                                                    (FStar_TypeChecker_Common.NonTrivial
                                                                    fml) in
                                                                 [uu____4643] in
                                                               g_guard ::
                                                                 uu____4640 in
                                                             f_guard ::
                                                               uu____4637 in
                                                           g_uvars ::
                                                             uu____4634 in
                                                         FStar_TypeChecker_Env.conj_guards
                                                           uu____4631 in
                                                       (let uu____4645 =
                                                          FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "ResolveImplicitsHook") in
                                                        if uu____4645
                                                        then
                                                          let uu____4650 =
                                                            let uu____4652 =
                                                              FStar_TypeChecker_Env.get_range
                                                                env in
                                                            FStar_Range.string_of_range
                                                              uu____4652 in
                                                          let uu____4653 =
                                                            FStar_TypeChecker_Rel.guard_to_string
                                                              env guard in
                                                          FStar_Util.print2
                                                            "///////////////////////////////EndBind at %s/////////////////////\nguard = %s\n"
                                                            uu____4650
                                                            uu____4653
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
                let uu____4702 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m in
                  let uu____4728 = FStar_TypeChecker_Env.wp_signature env m in
                  match uu____4728 with
                  | (a, kwp) ->
                      let uu____4759 = destruct_wp_comp ct1 in
                      let uu____4766 = destruct_wp_comp ct2 in
                      ((md, a, kwp), uu____4759, uu____4766) in
                match uu____4702 with
                | ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None ->
                          let uu____4819 = FStar_Syntax_Syntax.null_binder t1 in
                          [uu____4819]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____4839 = FStar_Syntax_Syntax.mk_binder x in
                          [uu____4839] in
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
                      let uu____4886 = FStar_Syntax_Syntax.as_arg r11 in
                      let uu____4895 =
                        let uu____4906 = FStar_Syntax_Syntax.as_arg t1 in
                        let uu____4915 =
                          let uu____4926 = FStar_Syntax_Syntax.as_arg t2 in
                          let uu____4935 =
                            let uu____4946 = FStar_Syntax_Syntax.as_arg wp1 in
                            let uu____4955 =
                              let uu____4966 =
                                let uu____4975 = mk_lam wp2 in
                                FStar_Syntax_Syntax.as_arg uu____4975 in
                              [uu____4966] in
                            uu____4946 :: uu____4955 in
                          uu____4926 :: uu____4935 in
                        uu____4906 :: uu____4915 in
                      uu____4886 :: uu____4895 in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator in
                    let wp =
                      let uu____5026 =
                        FStar_TypeChecker_Env.inst_effect_fun_with
                          [u_t1; u_t2] env md bind_wp in
                      FStar_Syntax_Syntax.mk_Tm_app uu____5026 wp_args
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
              let uu____5074 =
                let uu____5079 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1 in
                let uu____5080 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2 in
                (uu____5079, uu____5080) in
              match uu____5074 with
              | (ct1, ct2) ->
                  let uu____5087 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name in
                  (match uu____5087 with
                   | FStar_Pervasives_Native.Some (p, f_bind) ->
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None ->
                       let uu____5138 = lift_comps env c1 c2 b true in
                       (match uu____5138 with
                        | (m, c11, c21, g_lift) ->
                            let uu____5156 =
                              let uu____5161 =
                                FStar_Syntax_Util.comp_to_comp_typ c11 in
                              let uu____5162 =
                                FStar_Syntax_Util.comp_to_comp_typ c21 in
                              (uu____5161, uu____5162) in
                            (match uu____5156 with
                             | (ct11, ct21) ->
                                 let uu____5169 =
                                   let uu____5174 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m in
                                   if uu____5174
                                   then
                                     let bind_t =
                                       let uu____5182 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env) in
                                       FStar_All.pipe_right uu____5182
                                         FStar_Syntax_Util.get_bind_vc_combinator in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu____5185 =
                                        mk_wp_bind env m ct11 b ct21 flags r1 in
                                      (uu____5185,
                                        FStar_TypeChecker_Env.trivial_guard)) in
                                 (match uu____5169 with
                                  | (c, g_bind) ->
                                      let uu____5192 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind in
                                      (c, uu____5192)))))
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
            let uu____5228 =
              let uu____5229 =
                let uu____5240 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg in
                [uu____5240] in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____5229;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____5228 in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags ->
    let uu____5285 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_5291 ->
              match uu___1_5291 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> true
              | uu____5294 -> false)) in
    if uu____5285
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_5306 ->
              match uu___2_5306 with
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
        let uu____5334 = FStar_Syntax_Util.is_ml_comp c in
        if uu____5334
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
           let pure_assume_wp =
             let uu____5345 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None in
             FStar_Syntax_Syntax.fv_to_tm uu____5345 in
           let pure_assume_wp1 =
             let uu____5348 =
               let uu____5349 =
                 FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula in
               [uu____5349] in
             let uu____5382 = FStar_TypeChecker_Env.get_range env in
             FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____5348
               uu____5382 in
           let uu____5383 = weaken_flags ct.FStar_Syntax_Syntax.flags in
           bind_pure_wp_with env pure_assume_wp1 c uu____5383)
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env ->
    fun lc ->
      fun f ->
        let weaken uu____5411 =
          let uu____5412 = FStar_TypeChecker_Common.lcomp_comp lc in
          match uu____5412 with
          | (c, g_c) ->
              let uu____5423 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
              if uu____5423
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5437 = weaken_comp env c f1 in
                     (match uu____5437 with
                      | (c1, g_w) ->
                          let uu____5448 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w in
                          (c1, uu____5448))) in
        let uu____5449 = weaken_flags lc.FStar_TypeChecker_Common.cflags in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5449 weaken
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
                 let uu____5506 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None in
                 FStar_Syntax_Syntax.fv_to_tm uu____5506 in
               let pure_assert_wp1 =
                 let uu____5509 =
                   let uu____5510 =
                     let uu____5519 = label_opt env reason r f in
                     FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                       uu____5519 in
                   [uu____5510] in
                 FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____5509 r in
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
            let uu____5589 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0 in
            if uu____5589
            then (lc, g0)
            else
              (let flags =
                 let uu____5601 =
                   let uu____5609 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc in
                   if uu____5609
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, []) in
                 match uu____5601 with
                 | (maybe_trivial_post, flags) ->
                     let uu____5639 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_5647 ->
                               match uu___3_5647 with
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
                               | uu____5650 -> [])) in
                     FStar_List.append flags uu____5639 in
               let strengthen uu____5660 =
                 let uu____5661 = FStar_TypeChecker_Common.lcomp_comp lc in
                 match uu____5661 with
                 | (c, g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                        let uu____5680 = FStar_TypeChecker_Env.guard_form g01 in
                        match uu____5680 with
                        | FStar_TypeChecker_Common.Trivial -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____5687 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____5687
                              then
                                let uu____5691 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only in
                                let uu____5693 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____5691 uu____5693
                              else ());
                             (let uu____5698 =
                                strengthen_comp env reason c f flags in
                              match uu____5698 with
                              | (c1, g_s) ->
                                  let uu____5709 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s in
                                  (c1, uu____5709)))) in
               let uu____5710 =
                 let uu____5711 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name in
                 FStar_TypeChecker_Common.mk_lcomp uu____5711
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen in
               (uu____5710,
                 (let uu___678_5713 = g0 in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred_to_tac =
                      (uu___678_5713.FStar_TypeChecker_Common.deferred_to_tac);
                    FStar_TypeChecker_Common.deferred =
                      (uu___678_5713.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___678_5713.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___678_5713.FStar_TypeChecker_Common.implicits)
                  })))
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_5722 ->
            match uu___4_5722 with
            | FStar_Syntax_Syntax.SOMETRIVIAL -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION -> true
            | uu____5726 -> false) lc.FStar_TypeChecker_Common.cflags)
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
          let uu____5755 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax in
          if uu____5755
          then e
          else
            (let uu____5762 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____5765 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid in
                  FStar_Option.isSome uu____5765) in
             if uu____5762
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
                | uu____5835 -> false in
              if is_unit
              then
                let uu____5842 =
                  let uu____5844 =
                    let uu____5845 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name in
                    FStar_All.pipe_right uu____5845
                      (FStar_TypeChecker_Env.norm_eff_name env) in
                  FStar_All.pipe_right uu____5844
                    (FStar_TypeChecker_Env.is_layered_effect env) in
                (if uu____5842
                 then
                   let uu____5854 = FStar_Syntax_Subst.open_term_bv b phi in
                   match uu____5854 with
                   | (b1, phi1) ->
                       let phi2 =
                         FStar_Syntax_Subst.subst
                           [FStar_Syntax_Syntax.NT
                              (b1, FStar_Syntax_Syntax.unit_const)] phi1 in
                       weaken_comp env c phi2
                 else
                   (let uu____5870 = close_wp_comp env [x] c in
                    (uu____5870, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____5873 -> (c, FStar_TypeChecker_Env.trivial_guard)
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
          fun uu____5901 ->
            match uu____5901 with
            | (b, lc2) ->
                let debug f =
                  let uu____5921 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____5921 then f () else () in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                let bind_flags =
                  let uu____5934 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21) in
                  if uu____5934
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____5944 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11 in
                       if uu____5944
                       then
                         let uu____5949 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21 in
                         (if uu____5949
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5956 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21 in
                             if uu____5956
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5965 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21) in
                          if uu____5965
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else []) in
                     let uu____5972 = lcomp_has_trivial_postcondition lc21 in
                     if uu____5972
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags) in
                let bind_it uu____5988 =
                  let uu____5989 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ()) in
                  if uu____5989
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ in
                    let uu____5997 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ [] in
                    (uu____5997, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____6000 =
                       FStar_TypeChecker_Common.lcomp_comp lc11 in
                     match uu____6000 with
                     | (c1, g_c1) ->
                         let uu____6011 =
                           FStar_TypeChecker_Common.lcomp_comp lc21 in
                         (match uu____6011 with
                          | (c2, g_c2) ->
                              let trivial_guard =
                                let uu____6023 =
                                  match b with
                                  | FStar_Pervasives_Native.Some x ->
                                      let b1 =
                                        FStar_Syntax_Syntax.mk_binder x in
                                      let uu____6026 =
                                        FStar_Syntax_Syntax.is_null_binder b1 in
                                      if uu____6026
                                      then g_c2
                                      else
                                        FStar_TypeChecker_Env.close_guard env
                                          [b1] g_c2
                                  | FStar_Pervasives_Native.None -> g_c2 in
                                FStar_TypeChecker_Env.conj_guard g_c1
                                  uu____6023 in
                              (debug
                                 (fun uu____6052 ->
                                    let uu____6053 =
                                      FStar_Syntax_Print.comp_to_string c1 in
                                    let uu____6055 =
                                      match b with
                                      | FStar_Pervasives_Native.None ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x in
                                    let uu____6060 =
                                      FStar_Syntax_Print.comp_to_string c2 in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____6053 uu____6055 uu____6060);
                               (let aux uu____6078 =
                                  let uu____6079 =
                                    FStar_Syntax_Util.is_trivial_wp c1 in
                                  if uu____6079
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____6110
                                        ->
                                        let uu____6111 =
                                          FStar_Syntax_Util.is_ml_comp c2 in
                                        (if uu____6111
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____6143 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2) in
                                     if uu____6143
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML") in
                                let try_simplify uu____6190 =
                                  let aux_with_trivial_guard uu____6220 =
                                    let uu____6221 = aux () in
                                    match uu____6221 with
                                    | FStar_Util.Inl (c, reason) ->
                                        FStar_Util.Inl
                                          (c, trivial_guard, reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason in
                                  let uu____6279 =
                                    let uu____6281 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid in
                                    FStar_Option.isNone uu____6281 in
                                  if uu____6279
                                  then
                                    let uu____6297 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2) in
                                    (if uu____6297
                                     then
                                       FStar_Util.Inl
                                         (c2, trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____6324 =
                                          FStar_TypeChecker_Env.get_range env in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____6324))
                                  else
                                    (let uu____6341 =
                                       FStar_Syntax_Util.is_total_comp c1 in
                                     if uu____6341
                                     then
                                       let close_with_type_of_x x c =
                                         let x1 =
                                           let uu___781_6372 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___781_6372.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___781_6372.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         maybe_capture_unit_refinement env
                                           x1.FStar_Syntax_Syntax.sort x1 c in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some e,
                                          FStar_Pervasives_Native.Some x) ->
                                           let uu____6403 =
                                             let uu____6408 =
                                               FStar_All.pipe_right c2
                                                 (FStar_Syntax_Subst.subst_comp
                                                    [FStar_Syntax_Syntax.NT
                                                       (x, e)]) in
                                             FStar_All.pipe_right uu____6408
                                               (close_with_type_of_x x) in
                                           (match uu____6403 with
                                            | (c21, g_close) ->
                                                let uu____6429 =
                                                  let uu____6437 =
                                                    let uu____6438 =
                                                      let uu____6441 =
                                                        let uu____6444 =
                                                          FStar_TypeChecker_Env.map_guard
                                                            g_c2
                                                            (FStar_Syntax_Subst.subst
                                                               [FStar_Syntax_Syntax.NT
                                                                  (x, e)]) in
                                                        [uu____6444; g_close] in
                                                      g_c1 :: uu____6441 in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6438 in
                                                  (c21, uu____6437, "c1 Tot") in
                                                FStar_Util.Inl uu____6429)
                                       | (uu____6457,
                                          FStar_Pervasives_Native.Some x) ->
                                           let uu____6469 =
                                             FStar_All.pipe_right c2
                                               (close_with_type_of_x x) in
                                           (match uu____6469 with
                                            | (c21, g_close) ->
                                                let uu____6492 =
                                                  let uu____6500 =
                                                    let uu____6501 =
                                                      let uu____6504 =
                                                        let uu____6507 =
                                                          let uu____6508 =
                                                            let uu____6509 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x in
                                                            [uu____6509] in
                                                          FStar_TypeChecker_Env.close_guard
                                                            env uu____6508
                                                            g_c2 in
                                                        [uu____6507; g_close] in
                                                      g_c1 :: uu____6504 in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6501 in
                                                  (c21, uu____6500,
                                                    "c1 Tot only close") in
                                                FStar_Util.Inl uu____6492)
                                       | (uu____6538, uu____6539) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____6554 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2) in
                                        if uu____6554
                                        then
                                          let uu____6569 =
                                            let uu____6577 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2) in
                                            (uu____6577, trivial_guard,
                                              "both GTot") in
                                          FStar_Util.Inl uu____6569
                                        else aux_with_trivial_guard ())) in
                                let uu____6590 = try_simplify () in
                                match uu____6590 with
                                | FStar_Util.Inl (c, g, reason) ->
                                    (debug
                                       (fun uu____6625 ->
                                          let uu____6626 =
                                            FStar_Syntax_Print.comp_to_string
                                              c in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____6626);
                                     (c, g))
                                | FStar_Util.Inr reason ->
                                    (debug
                                       (fun uu____6642 ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 g =
                                        let uu____6673 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1 in
                                        match uu____6673 with
                                        | (c, g_bind) ->
                                            let uu____6684 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g g_bind in
                                            (c, uu____6684) in
                                      let mk_seq c11 b1 c21 =
                                        let c12 =
                                          FStar_TypeChecker_Env.unfold_effect_abbrev
                                            env c11 in
                                        let c22 =
                                          FStar_TypeChecker_Env.unfold_effect_abbrev
                                            env c21 in
                                        let uu____6711 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name in
                                        match uu____6711 with
                                        | (m, uu____6723, lift2) ->
                                            let uu____6725 =
                                              lift_comp env c22 lift2 in
                                            (match uu____6725 with
                                             | (c23, g2) ->
                                                 let uu____6736 =
                                                   destruct_wp_comp c12 in
                                                 (match uu____6736 with
                                                  | (u1, t1, wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name in
                                                      let trivial =
                                                        let uu____6752 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator in
                                                        FStar_All.pipe_right
                                                          uu____6752
                                                          FStar_Util.must in
                                                      let vc1 =
                                                        let uu____6760 =
                                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                                            [u1] env
                                                            md_pure_or_ghost
                                                            trivial in
                                                        let uu____6761 =
                                                          let uu____6762 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              t1 in
                                                          let uu____6771 =
                                                            let uu____6782 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                wp1 in
                                                            [uu____6782] in
                                                          uu____6762 ::
                                                            uu____6771 in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____6760
                                                          uu____6761 r1 in
                                                      let uu____6815 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags in
                                                      (match uu____6815 with
                                                       | (c, g_s) ->
                                                           let uu____6830 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s] in
                                                           (c, uu____6830)))) in
                                      let uu____6831 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1 in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None ->
                                            let uu____6847 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t in
                                            (uu____6847, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t) in
                                      match uu____6831 with
                                      | (u_res_t1, res_t1) ->
                                          let uu____6863 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11) in
                                          if uu____6863
                                          then
                                            let e1 = FStar_Option.get e1opt in
                                            let x = FStar_Option.get b in
                                            let uu____6872 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1 in
                                            (if uu____6872
                                             then
                                               (debug
                                                  (fun uu____6886 ->
                                                     let uu____6887 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1 in
                                                     let uu____6889 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____6887 uu____6889);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2 in
                                                 let g =
                                                   let uu____6896 =
                                                     FStar_TypeChecker_Env.map_guard
                                                       g_c2
                                                       (FStar_Syntax_Subst.subst
                                                          [FStar_Syntax_Syntax.NT
                                                             (x, e1)]) in
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 uu____6896 in
                                                 mk_bind1 c1 b c21 g))
                                             else
                                               (let uu____6901 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____6904 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid in
                                                     FStar_Option.isSome
                                                       uu____6904) in
                                                if uu____6901
                                                then
                                                  let e1' =
                                                    let uu____6929 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        () in
                                                    if uu____6929
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1 in
                                                  (debug
                                                     (fun uu____6941 ->
                                                        let uu____6942 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1' in
                                                        let uu____6944 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____6942
                                                          uu____6944);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2 in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug
                                                     (fun uu____6959 ->
                                                        let uu____6960 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1 in
                                                        let uu____6962 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____6960
                                                          uu____6962);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2 in
                                                    let x_eq_e =
                                                      let uu____6969 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____6969 in
                                                    let uu____6970 =
                                                      let uu____6975 =
                                                        let uu____6976 =
                                                          let uu____6977 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x in
                                                          [uu____6977] in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____6976 in
                                                      weaken_comp uu____6975
                                                        c21 x_eq_e in
                                                    match uu____6970 with
                                                    | (c22, g_w) ->
                                                        let g =
                                                          let uu____7003 =
                                                            let uu____7006 =
                                                              let uu____7009
                                                                =
                                                                let uu____7010
                                                                  =
                                                                  let uu____7011
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x in
                                                                  [uu____7011] in
                                                                FStar_TypeChecker_Env.close_guard
                                                                  env
                                                                  uu____7010
                                                                  g_w in
                                                              let uu____7030
                                                                =
                                                                let uu____7033
                                                                  =
                                                                  let uu____7034
                                                                    =
                                                                    let uu____7035
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x in
                                                                    [uu____7035] in
                                                                  let uu____7054
                                                                    =
                                                                    FStar_TypeChecker_Common.weaken_guard_formula
                                                                    g_c2
                                                                    x_eq_e in
                                                                  FStar_TypeChecker_Env.close_guard
                                                                    env
                                                                    uu____7034
                                                                    uu____7054 in
                                                                [uu____7033] in
                                                              uu____7009 ::
                                                                uu____7030 in
                                                            g_c1 ::
                                                              uu____7006 in
                                                          FStar_TypeChecker_Env.conj_guards
                                                            uu____7003 in
                                                        mk_bind1 c1 b c22 g))))
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
      | uu____7071 -> g2
let (assume_result_eq_pure_term_in_m :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env ->
    fun m_opt ->
      fun e ->
        fun lc ->
          let m =
            let uu____7102 =
              (FStar_All.pipe_right m_opt FStar_Util.is_none) ||
                (is_ghost_effect env lc.FStar_TypeChecker_Common.eff_name) in
            if uu____7102
            then FStar_Parser_Const.effect_PURE_lid
            else FStar_All.pipe_right m_opt FStar_Util.must in
          let flags =
            let uu____7115 = FStar_TypeChecker_Common.is_total_lcomp lc in
            if uu____7115
            then FStar_Syntax_Syntax.RETURN ::
              (lc.FStar_TypeChecker_Common.cflags)
            else FStar_Syntax_Syntax.PARTIAL_RETURN ::
              (lc.FStar_TypeChecker_Common.cflags) in
          let refine uu____7131 =
            let uu____7136 = FStar_TypeChecker_Common.lcomp_comp lc in
            match uu____7136 with
            | (c, g_c) ->
                let u_t =
                  match comp_univ_opt c with
                  | FStar_Pervasives_Native.Some u_t -> u_t
                  | FStar_Pervasives_Native.None ->
                      env.FStar_TypeChecker_Env.universe_of env
                        (FStar_Syntax_Util.comp_result c) in
                let uu____7149 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____7149
                then
                  let uu____7156 =
                    return_value env m (FStar_Pervasives_Native.Some u_t)
                      (FStar_Syntax_Util.comp_result c) e in
                  (match uu____7156 with
                   | (retc, g_retc) ->
                       let g_c1 = FStar_TypeChecker_Env.conj_guard g_c g_retc in
                       let uu____7168 =
                         let uu____7170 = FStar_Syntax_Util.is_pure_comp c in
                         Prims.op_Negation uu____7170 in
                       if uu____7168
                       then
                         let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                         let retc2 =
                           let uu___907_7179 = retc1 in
                           {
                             FStar_Syntax_Syntax.comp_univs =
                               (uu___907_7179.FStar_Syntax_Syntax.comp_univs);
                             FStar_Syntax_Syntax.effect_name =
                               FStar_Parser_Const.effect_GHOST_lid;
                             FStar_Syntax_Syntax.result_typ =
                               (uu___907_7179.FStar_Syntax_Syntax.result_typ);
                             FStar_Syntax_Syntax.effect_args =
                               (uu___907_7179.FStar_Syntax_Syntax.effect_args);
                             FStar_Syntax_Syntax.flags = flags
                           } in
                         let uu____7180 = FStar_Syntax_Syntax.mk_Comp retc2 in
                         (uu____7180, g_c1)
                       else
                         (let uu____7183 =
                            FStar_Syntax_Util.comp_set_flags retc flags in
                          (uu____7183, g_c1)))
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
                   let uu____7194 =
                     return_value env_x m (FStar_Pervasives_Native.Some u_t)
                       t xexp in
                   match uu____7194 with
                   | (ret, g_ret) ->
                       let ret1 =
                         let uu____7206 =
                           FStar_Syntax_Util.comp_set_flags ret
                             [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                         FStar_All.pipe_left
                           FStar_TypeChecker_Common.lcomp_of_comp uu____7206 in
                       let eq = FStar_Syntax_Util.mk_eq2 u_t t xexp e in
                       let eq_ret =
                         weaken_precondition env_x ret1
                           (FStar_TypeChecker_Common.NonTrivial eq) in
                       let uu____7209 =
                         let uu____7214 =
                           let uu____7215 =
                             FStar_TypeChecker_Common.lcomp_of_comp c2 in
                           bind e.FStar_Syntax_Syntax.pos env
                             FStar_Pervasives_Native.None uu____7215
                             ((FStar_Pervasives_Native.Some x), eq_ret) in
                         FStar_TypeChecker_Common.lcomp_comp uu____7214 in
                       (match uu____7209 with
                        | (bind_c, g_bind) ->
                            let uu____7224 =
                              FStar_Syntax_Util.comp_set_flags bind_c flags in
                            let uu____7225 =
                              FStar_TypeChecker_Env.conj_guards
                                [g_c; g_ret; g_bind] in
                            (uu____7224, uu____7225))) in
          let uu____7226 = should_not_inline_lc lc in
          if uu____7226
          then
            let uu____7229 =
              let uu____7235 =
                let uu____7237 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format1
                  "assume_result_eq_pure_term cannot inline an non-inlineable lc : %s"
                  uu____7237 in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____7235) in
            FStar_Errors.raise_error uu____7229 e.FStar_Syntax_Syntax.pos
          else
            (let uu____7243 = refine () in
             match uu____7243 with
             | (c, g) -> FStar_TypeChecker_Common.lcomp_of_comp_guard c g)
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
              (let uu____7278 =
                 FStar_TypeChecker_Common.is_lcomp_partial_return lc in
               Prims.op_Negation uu____7278) in
          if Prims.op_Negation should_return1
          then lc
          else assume_result_eq_pure_term_in_m env m_opt e lc
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
            fun uu____7331 ->
              match uu____7331 with
              | (x, lc2) ->
                  let env_x =
                    match x with
                    | FStar_Pervasives_Native.None -> env
                    | FStar_Pervasives_Native.Some x1 ->
                        FStar_TypeChecker_Env.push_bv env x1 in
                  let lc21 =
                    let eff1 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc1.FStar_TypeChecker_Common.eff_name in
                    let eff2 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc2.FStar_TypeChecker_Common.eff_name in
                    let uu____7345 =
                      ((FStar_Ident.lid_equals eff2
                          FStar_Parser_Const.effect_PURE_lid)
                         &&
                         (let uu____7348 =
                            FStar_TypeChecker_Env.join_opt env eff1 eff2 in
                          FStar_All.pipe_right uu____7348 FStar_Util.is_none))
                        &&
                        (let uu____7373 =
                           FStar_TypeChecker_Env.exists_polymonadic_bind env
                             eff1 eff2 in
                         FStar_All.pipe_right uu____7373 FStar_Util.is_none) in
                    if uu____7345
                    then
                      let uu____7410 =
                        FStar_All.pipe_right eff1
                          (fun uu____7415 ->
                             FStar_Pervasives_Native.Some uu____7415) in
                      assume_result_eq_pure_term_in_m env_x uu____7410 e2 lc2
                    else
                      (let uu____7418 =
                         ((let uu____7422 = is_pure_or_ghost_effect env eff1 in
                           Prims.op_Negation uu____7422) ||
                            (should_not_inline_lc lc1))
                           && (is_pure_or_ghost_effect env eff2) in
                       if uu____7418
                       then
                         let uu____7425 =
                           FStar_All.pipe_right eff1
                             (fun uu____7430 ->
                                FStar_Pervasives_Native.Some uu____7430) in
                         maybe_assume_result_eq_pure_term_in_m env_x
                           uu____7425 e2 lc2
                       else lc2) in
                  bind r env e1opt lc1 (x, lc21)
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun lid ->
      let uu____7446 =
        let uu____7447 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____7447 in
      FStar_Syntax_Syntax.fvar uu____7446 FStar_Syntax_Syntax.delta_constant
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
                    let uu____7499 =
                      FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                    FStar_Util.format1 "%s.conjunction" uu____7499 in
                  let uu____7502 =
                    let uu____7507 =
                      let uu____7508 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator in
                      FStar_All.pipe_right uu____7508 FStar_Util.must in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7507 [u_a] in
                  match uu____7502 with
                  | (uu____7519, conjunction) ->
                      let uu____7521 =
                        let uu____7530 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args in
                        let uu____7545 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args in
                        (uu____7530, uu____7545) in
                      (match uu____7521 with
                       | (is1, is2) ->
                           let conjunction_t_error s =
                             let uu____7591 =
                               let uu____7593 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction in
                               FStar_Util.format3
                                 "conjunction %s (%s) does not have proper shape (reason:%s)"
                                 uu____7593 conjunction_name s in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7591) in
                           let uu____7597 =
                             let uu____7642 =
                               let uu____7643 =
                                 FStar_Syntax_Subst.compress conjunction in
                               uu____7643.FStar_Syntax_Syntax.n in
                             match uu____7642 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs, body, uu____7692) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____7724 =
                                   FStar_Syntax_Subst.open_term bs body in
                                 (match uu____7724 with
                                  | (a_b::bs1, body1) ->
                                      let uu____7796 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1 in
                                      (match uu____7796 with
                                       | (rest_bs, f_b::g_b::p_b::[]) ->
                                           let uu____7944 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____7944)))
                             | uu____7977 ->
                                 let uu____7978 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders" in
                                 FStar_Errors.raise_error uu____7978 r in
                           (match uu____7597 with
                            | (a_b, rest_bs, f_b, g_b, p_b, body) ->
                                let uu____8103 =
                                  let uu____8110 =
                                    let uu____8111 =
                                      let uu____8112 =
                                        let uu____8119 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst in
                                        (uu____8119, a) in
                                      FStar_Syntax_Syntax.NT uu____8112 in
                                    [uu____8111] in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____8110
                                    (fun b ->
                                       let uu____8135 =
                                         FStar_Syntax_Print.binder_to_string
                                           b in
                                       let uu____8137 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname in
                                       let uu____8139 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____8135 uu____8137 uu____8139) r in
                                (match uu____8103 with
                                 | (rest_bs_uvars, g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b ->
                                            fun t ->
                                              let uu____8177 =
                                                let uu____8184 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst in
                                                (uu____8184, t) in
                                              FStar_Syntax_Syntax.NT
                                                uu____8177) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p])) in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____8223 =
                                           let uu____8224 =
                                             let uu____8227 =
                                               let uu____8228 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst in
                                               uu____8228.FStar_Syntax_Syntax.sort in
                                             FStar_Syntax_Subst.compress
                                               uu____8227 in
                                           uu____8224.FStar_Syntax_Syntax.n in
                                         match uu____8223 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8239, uu____8240::is) ->
                                             let uu____8282 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst) in
                                             FStar_All.pipe_right uu____8282
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8315 ->
                                             let uu____8316 =
                                               conjunction_t_error
                                                 "f's type is not a repr type" in
                                             FStar_Errors.raise_error
                                               uu____8316 r in
                                       FStar_List.fold_left2
                                         (fun g ->
                                            fun i1 ->
                                              fun f_i ->
                                                let uu____8332 =
                                                  FStar_TypeChecker_Rel.layered_effect_teq
                                                    env i1 f_i
                                                    (FStar_Pervasives_Native.Some
                                                       conjunction_name) in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8332)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____8338 =
                                           let uu____8339 =
                                             let uu____8342 =
                                               let uu____8343 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst in
                                               uu____8343.FStar_Syntax_Syntax.sort in
                                             FStar_Syntax_Subst.compress
                                               uu____8342 in
                                           uu____8339.FStar_Syntax_Syntax.n in
                                         match uu____8338 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8354, uu____8355::is) ->
                                             let uu____8397 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst) in
                                             FStar_All.pipe_right uu____8397
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8430 ->
                                             let uu____8431 =
                                               conjunction_t_error
                                                 "g's type is not a repr type" in
                                             FStar_Errors.raise_error
                                               uu____8431 r in
                                       FStar_List.fold_left2
                                         (fun g ->
                                            fun i2 ->
                                              fun g_i ->
                                                let uu____8447 =
                                                  FStar_TypeChecker_Rel.layered_effect_teq
                                                    env i2 g_i
                                                    (FStar_Pervasives_Native.Some
                                                       conjunction_name) in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8447)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body in
                                     let is =
                                       let uu____8453 =
                                         let uu____8454 =
                                           FStar_Syntax_Subst.compress body1 in
                                         uu____8454.FStar_Syntax_Syntax.n in
                                       match uu____8453 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8459, a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8514 ->
                                           let uu____8515 =
                                             conjunction_t_error
                                               "body is not a repr type" in
                                           FStar_Errors.raise_error
                                             uu____8515 r in
                                     let uu____8524 =
                                       let uu____8525 =
                                         let uu____8526 =
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
                                             uu____8526;
                                           FStar_Syntax_Syntax.flags = []
                                         } in
                                       FStar_Syntax_Syntax.mk_Comp uu____8525 in
                                     let uu____8549 =
                                       let uu____8550 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8550 g_guard in
                                     (uu____8524, uu____8549))))
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
                fun uu____8595 ->
                  let p1 = FStar_Syntax_Util.b2t p in
                  let if_then_else =
                    let uu____8604 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator in
                    FStar_All.pipe_right uu____8604 FStar_Util.must in
                  let uu____8611 = destruct_wp_comp ct1 in
                  match uu____8611 with
                  | (uu____8622, uu____8623, wp_t) ->
                      let uu____8625 = destruct_wp_comp ct2 in
                      (match uu____8625 with
                       | (uu____8636, uu____8637, wp_e) ->
                           let wp =
                             let uu____8640 =
                               FStar_TypeChecker_Env.inst_effect_fun_with
                                 [u_a] env ed if_then_else in
                             let uu____8641 =
                               let uu____8642 = FStar_Syntax_Syntax.as_arg a in
                               let uu____8651 =
                                 let uu____8662 =
                                   FStar_Syntax_Syntax.as_arg p1 in
                                 let uu____8671 =
                                   let uu____8682 =
                                     FStar_Syntax_Syntax.as_arg wp_t in
                                   let uu____8691 =
                                     let uu____8702 =
                                       FStar_Syntax_Syntax.as_arg wp_e in
                                     [uu____8702] in
                                   uu____8682 :: uu____8691 in
                                 uu____8662 :: uu____8671 in
                               uu____8642 :: uu____8651 in
                             let uu____8751 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Syntax.mk_Tm_app uu____8640
                               uu____8641 uu____8751 in
                           let uu____8752 = mk_comp ed u_a a wp [] in
                           (uu____8752, FStar_TypeChecker_Env.trivial_guard))
let (comp_pure_wp_false :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun u ->
      fun t ->
        let post_k =
          let uu____8772 =
            let uu____8781 = FStar_Syntax_Syntax.null_binder t in
            [uu____8781] in
          let uu____8800 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
          FStar_Syntax_Util.arrow uu____8772 uu____8800 in
        let kwp =
          let uu____8806 =
            let uu____8815 = FStar_Syntax_Syntax.null_binder post_k in
            [uu____8815] in
          let uu____8834 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
          FStar_Syntax_Util.arrow uu____8806 uu____8834 in
        let post =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k in
        let wp =
          let uu____8841 =
            let uu____8842 = FStar_Syntax_Syntax.mk_binder post in
            [uu____8842] in
          let uu____8861 = fvar_const env FStar_Parser_Const.false_lid in
          FStar_Syntax_Util.abs uu____8841 uu____8861
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
            let uu____8920 =
              let uu____8921 =
                FStar_All.pipe_right scrutinee FStar_Syntax_Syntax.mk_binder in
              [uu____8921] in
            FStar_TypeChecker_Env.push_binders env0 uu____8920 in
          let eff =
            FStar_List.fold_left
              (fun eff ->
                 fun uu____8968 ->
                   match uu____8968 with
                   | (uu____8982, eff_label, uu____8984, uu____8985) ->
                       join_effects env eff eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases in
          let uu____8998 =
            let uu____9006 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu____9044 ->
                      match uu____9044 with
                      | (uu____9059, uu____9060, flags, uu____9062) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___5_9079 ->
                                  match uu___5_9079 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE ->
                                      true
                                  | uu____9082 -> false)))) in
            if uu____9006
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, []) in
          match uu____8998 with
          | (should_not_inline_whole_match, bind_cases_flags) ->
              let bind_cases uu____9119 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
                let uu____9121 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
                if uu____9121
                then
                  let uu____9128 = lax_mk_tot_or_comp_l eff u_res_t res_t [] in
                  (uu____9128, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let maybe_return eff_label_then cthen =
                     let uu____9149 =
                       should_not_inline_whole_match ||
                         (let uu____9152 = is_pure_or_ghost_effect env eff in
                          Prims.op_Negation uu____9152) in
                     if uu____9149 then cthen true else cthen false in
                   let uu____9159 =
                     let uu____9170 =
                       let uu____9183 =
                         let uu____9188 =
                           let uu____9199 =
                             FStar_All.pipe_right lcases
                               (FStar_List.map
                                  (fun uu____9249 ->
                                     match uu____9249 with
                                     | (g, uu____9268, uu____9269,
                                        uu____9270) -> g)) in
                           FStar_All.pipe_right uu____9199
                             (FStar_List.fold_left
                                (fun uu____9318 ->
                                   fun g ->
                                     match uu____9318 with
                                     | (conds, acc) ->
                                         let cond =
                                           let uu____9359 =
                                             let uu____9362 =
                                               FStar_All.pipe_right g
                                                 FStar_Syntax_Util.b2t in
                                             FStar_All.pipe_right uu____9362
                                               FStar_Syntax_Util.mk_neg in
                                           FStar_Syntax_Util.mk_conj acc
                                             uu____9359 in
                                         ((FStar_List.append conds [cond]),
                                           cond))
                                ([FStar_Syntax_Util.t_true],
                                  FStar_Syntax_Util.t_true)) in
                         FStar_All.pipe_right uu____9188
                           FStar_Pervasives_Native.fst in
                       FStar_All.pipe_right uu____9183
                         (fun l ->
                            FStar_List.splitAt
                              ((FStar_List.length l) - Prims.int_one) l) in
                     FStar_All.pipe_right uu____9170
                       (fun uu____9468 ->
                          match uu____9468 with
                          | (l1, l2) ->
                              let uu____9509 = FStar_List.hd l2 in
                              (l1, uu____9509)) in
                   match uu____9159 with
                   | (neg_branch_conds, exhaustiveness_branch_cond) ->
                       let uu____9538 =
                         match lcases with
                         | [] ->
                             let uu____9569 =
                               comp_pure_wp_false env u_res_t res_t in
                             (FStar_Pervasives_Native.None, uu____9569,
                               FStar_TypeChecker_Env.trivial_guard)
                         | uu____9572 ->
                             let uu____9589 =
                               let uu____9622 =
                                 let uu____9633 =
                                   FStar_All.pipe_right neg_branch_conds
                                     (FStar_List.splitAt
                                        ((FStar_List.length lcases) -
                                           Prims.int_one)) in
                                 FStar_All.pipe_right uu____9633
                                   (fun uu____9705 ->
                                      match uu____9705 with
                                      | (l1, l2) ->
                                          let uu____9746 = FStar_List.hd l2 in
                                          (l1, uu____9746)) in
                               match uu____9622 with
                               | (neg_branch_conds1, neg_last) ->
                                   let uu____9803 =
                                     let uu____9842 =
                                       FStar_All.pipe_right lcases
                                         (FStar_List.splitAt
                                            ((FStar_List.length lcases) -
                                               Prims.int_one)) in
                                     FStar_All.pipe_right uu____9842
                                       (fun uu____10054 ->
                                          match uu____10054 with
                                          | (l1, l2) ->
                                              let uu____10205 =
                                                FStar_List.hd l2 in
                                              (l1, uu____10205)) in
                                   (match uu____9803 with
                                    | (lcases1,
                                       (g_last, eff_last, uu____10307,
                                        c_last)) ->
                                        let uu____10377 =
                                          let lc =
                                            maybe_return eff_last c_last in
                                          let uu____10383 =
                                            FStar_TypeChecker_Common.lcomp_comp
                                              lc in
                                          match uu____10383 with
                                          | (c, g) ->
                                              let uu____10394 =
                                                let uu____10395 =
                                                  let uu____10396 =
                                                    FStar_Syntax_Util.b2t
                                                      g_last in
                                                  FStar_Syntax_Util.mk_conj
                                                    uu____10396 neg_last in
                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                  g uu____10395 in
                                              (c, uu____10394) in
                                        (match uu____10377 with
                                         | (c, g) ->
                                             let uu____10433 =
                                               let uu____10434 =
                                                 FStar_All.pipe_right
                                                   eff_last
                                                   (FStar_TypeChecker_Env.norm_eff_name
                                                      env) in
                                               FStar_All.pipe_right
                                                 uu____10434
                                                 (FStar_TypeChecker_Env.get_effect_decl
                                                    env) in
                                             (lcases1, neg_branch_conds1,
                                               uu____10433, c, g))) in
                             (match uu____9589 with
                              | (lcases1, neg_branch_conds1, md, comp,
                                 g_comp) ->
                                  FStar_List.fold_right2
                                    (fun uu____10567 ->
                                       fun neg_cond ->
                                         fun uu____10569 ->
                                           match (uu____10567, uu____10569)
                                           with
                                           | ((g, eff_label, uu____10629,
                                               cthen),
                                              (uu____10631, celse, g_comp1))
                                               ->
                                               let uu____10678 =
                                                 let uu____10683 =
                                                   maybe_return eff_label
                                                     cthen in
                                                 FStar_TypeChecker_Common.lcomp_comp
                                                   uu____10683 in
                                               (match uu____10678 with
                                                | (cthen1, g_then) ->
                                                    let uu____10694 =
                                                      let uu____10705 =
                                                        lift_comps_sep_guards
                                                          env cthen1 celse
                                                          FStar_Pervasives_Native.None
                                                          false in
                                                      match uu____10705 with
                                                      | (m, cthen2, celse1,
                                                         g_lift_then,
                                                         g_lift_else) ->
                                                          let md1 =
                                                            FStar_TypeChecker_Env.get_effect_decl
                                                              env m in
                                                          let uu____10733 =
                                                            FStar_All.pipe_right
                                                              cthen2
                                                              FStar_Syntax_Util.comp_to_comp_typ in
                                                          let uu____10734 =
                                                            FStar_All.pipe_right
                                                              celse1
                                                              FStar_Syntax_Util.comp_to_comp_typ in
                                                          (md1, uu____10733,
                                                            uu____10734,
                                                            g_lift_then,
                                                            g_lift_else) in
                                                    (match uu____10694 with
                                                     | (md1, ct_then,
                                                        ct_else, g_lift_then,
                                                        g_lift_else) ->
                                                         let fn =
                                                           let uu____10785 =
                                                             FStar_All.pipe_right
                                                               md1
                                                               FStar_Syntax_Util.is_layered in
                                                           if uu____10785
                                                           then
                                                             mk_layered_conjunction
                                                           else
                                                             mk_non_layered_conjunction in
                                                         let uu____10819 =
                                                           let uu____10824 =
                                                             FStar_TypeChecker_Env.get_range
                                                               env in
                                                           fn env md1 u_res_t
                                                             res_t g ct_then
                                                             ct_else
                                                             uu____10824 in
                                                         (match uu____10819
                                                          with
                                                          | (c,
                                                             g_conjunction)
                                                              ->
                                                              let uu____10835
                                                                =
                                                                let g1 =
                                                                  FStar_Syntax_Util.b2t
                                                                    g in
                                                                let uu____10843
                                                                  =
                                                                  let uu____10844
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_then
                                                                    g_lift_then in
                                                                  let uu____10845
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    g1 in
                                                                  FStar_TypeChecker_Common.weaken_guard_formula
                                                                    uu____10844
                                                                    uu____10845 in
                                                                let uu____10846
                                                                  =
                                                                  let uu____10847
                                                                    =
                                                                    let uu____10848
                                                                    =
                                                                    FStar_Syntax_Util.mk_neg
                                                                    g1 in
                                                                    FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    uu____10848 in
                                                                  FStar_TypeChecker_Common.weaken_guard_formula
                                                                    g_lift_else
                                                                    uu____10847 in
                                                                (uu____10843,
                                                                  uu____10846) in
                                                              (match uu____10835
                                                               with
                                                               | (g_then1,
                                                                  g_else) ->
                                                                   let uu____10861
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guards
                                                                    [g_comp1;
                                                                    g_then1;
                                                                    g_else;
                                                                    g_conjunction] in
                                                                   ((FStar_Pervasives_Native.Some
                                                                    md1), c,
                                                                    uu____10861))))))
                                    lcases1 neg_branch_conds1
                                    ((FStar_Pervasives_Native.Some md), comp,
                                      g_comp)) in
                       (match uu____9538 with
                        | (md, comp, g_comp) ->
                            let uu____10877 =
                              let uu____10882 =
                                let check =
                                  FStar_Syntax_Util.mk_imp
                                    exhaustiveness_branch_cond
                                    FStar_Syntax_Util.t_false in
                                let check1 =
                                  let uu____10889 =
                                    FStar_TypeChecker_Env.get_range env in
                                  label
                                    FStar_TypeChecker_Err.exhaustiveness_check
                                    uu____10889 check in
                                strengthen_comp env
                                  FStar_Pervasives_Native.None comp check1
                                  bind_cases_flags in
                              match uu____10882 with
                              | (c, g) ->
                                  let uu____10900 =
                                    FStar_TypeChecker_Env.conj_guard g_comp g in
                                  (c, uu____10900) in
                            (match uu____10877 with
                             | (comp1, g_comp1) ->
                                 let g_comp2 =
                                   let uu____10908 =
                                     let uu____10909 =
                                       FStar_All.pipe_right scrutinee
                                         FStar_Syntax_Syntax.mk_binder in
                                     [uu____10909] in
                                   FStar_TypeChecker_Env.close_guard env0
                                     uu____10908 g_comp1 in
                                 (match lcases with
                                  | [] -> (comp1, g_comp2)
                                  | uu____10952::[] -> (comp1, g_comp2)
                                  | uu____10995 ->
                                      let uu____11012 =
                                        let uu____11014 =
                                          FStar_All.pipe_right md
                                            FStar_Util.must in
                                        FStar_All.pipe_right uu____11014
                                          FStar_Syntax_Util.is_layered in
                                      if uu____11012
                                      then (comp1, g_comp2)
                                      else
                                        (let comp2 =
                                           FStar_TypeChecker_Env.comp_to_comp_typ
                                             env comp1 in
                                         let md1 =
                                           FStar_TypeChecker_Env.get_effect_decl
                                             env
                                             comp2.FStar_Syntax_Syntax.effect_name in
                                         let uu____11027 =
                                           destruct_wp_comp comp2 in
                                         match uu____11027 with
                                         | (uu____11038, uu____11039, wp) ->
                                             let ite_wp =
                                               let uu____11042 =
                                                 FStar_All.pipe_right md1
                                                   FStar_Syntax_Util.get_wp_ite_combinator in
                                               FStar_All.pipe_right
                                                 uu____11042 FStar_Util.must in
                                             let wp1 =
                                               let uu____11050 =
                                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                                   [u_res_t] env md1 ite_wp in
                                               let uu____11051 =
                                                 let uu____11052 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     res_t in
                                                 let uu____11061 =
                                                   let uu____11072 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp in
                                                   [uu____11072] in
                                                 uu____11052 :: uu____11061 in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu____11050 uu____11051
                                                 wp.FStar_Syntax_Syntax.pos in
                                             let uu____11105 =
                                               mk_comp md1 u_res_t res_t wp1
                                                 bind_cases_flags in
                                             (uu____11105, g_comp2)))))) in
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
          let uu____11140 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____11140 with
          | FStar_Pervasives_Native.None ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____11156 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c' in
                let uu____11162 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error uu____11156 uu____11162
              else
                (let uu____11171 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c' in
                 let uu____11177 = FStar_TypeChecker_Env.get_range env in
                 FStar_Errors.raise_error uu____11171 uu____11177)
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
          let uu____11202 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name in
          FStar_All.pipe_right uu____11202
            (FStar_TypeChecker_Env.norm_eff_name env) in
        let uu____11205 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid in
        if uu____11205
        then u_res
        else
          (let is_total =
             let uu____11212 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid in
             FStar_All.pipe_right uu____11212
               (FStar_List.existsb
                  (fun q -> q = FStar_Syntax_Syntax.TotalEffect)) in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____11223 = FStar_TypeChecker_Env.effect_repr env c u_res in
              match uu____11223 with
              | FStar_Pervasives_Native.None ->
                  let uu____11226 =
                    let uu____11232 =
                      let uu____11234 =
                        FStar_Syntax_Print.lid_to_string c_lid in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____11234 in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____11232) in
                  FStar_Errors.raise_error uu____11226
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
      let uu____11258 = destruct_wp_comp ct in
      match uu____11258 with
      | (u_t, t, wp) ->
          let vc =
            let uu____11275 =
              let uu____11276 =
                let uu____11277 =
                  FStar_All.pipe_right md
                    FStar_Syntax_Util.get_wp_trivial_combinator in
                FStar_All.pipe_right uu____11277 FStar_Util.must in
              FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                uu____11276 in
            let uu____11284 =
              let uu____11285 = FStar_Syntax_Syntax.as_arg t in
              let uu____11294 =
                let uu____11305 = FStar_Syntax_Syntax.as_arg wp in
                [uu____11305] in
              uu____11285 :: uu____11294 in
            let uu____11338 = FStar_TypeChecker_Env.get_range env in
            FStar_Syntax_Syntax.mk_Tm_app uu____11275 uu____11284 uu____11338 in
          let uu____11339 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc) in
          (ct, vc, uu____11339)
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
                  let uu____11394 =
                    FStar_TypeChecker_Env.try_lookup_lid env f in
                  match uu____11394 with
                  | FStar_Pervasives_Native.Some uu____11409 ->
                      ((let uu____11427 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions") in
                        if uu____11427
                        then
                          let uu____11431 = FStar_Ident.string_of_lid f in
                          FStar_Util.print1 "Coercing with %s!\n" uu____11431
                        else ());
                       (let coercion =
                          let uu____11437 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos in
                          FStar_Syntax_Syntax.fvar uu____11437
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs in
                        let lc1 =
                          let uu____11444 =
                            let uu____11445 =
                              let uu____11446 = mkcomp ty in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____11446 in
                            (FStar_Pervasives_Native.None, uu____11445) in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____11444 in
                        let e1 =
                          let uu____11450 =
                            let uu____11451 = FStar_Syntax_Syntax.as_arg e in
                            [uu____11451] in
                          FStar_Syntax_Syntax.mk_Tm_app coercion2 uu____11450
                            e.FStar_Syntax_Syntax.pos in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None ->
                      ((let uu____11485 =
                          let uu____11491 =
                            let uu____11493 = FStar_Ident.string_of_lid f in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____11493 in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____11491) in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____11485);
                       (e, lc))
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee ->
    match projectee with | Yes _0 -> true | uu____11512 -> false
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee -> match projectee with | Yes _0 -> _0
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee ->
    match projectee with | Maybe -> true | uu____11530 -> false
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee -> match projectee with | No -> true | uu____11541 -> false
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
      let uu____11565 = FStar_Syntax_Util.head_and_args t2 in
      match uu____11565 with
      | (h, args) ->
          let h1 = FStar_Syntax_Util.un_uinst h in
          let r =
            let uu____11610 =
              let uu____11625 =
                let uu____11626 = FStar_Syntax_Subst.compress h1 in
                uu____11626.FStar_Syntax_Syntax.n in
              (uu____11625, args) in
            match uu____11610 with
            | (FStar_Syntax_Syntax.Tm_fvar fv,
               (a, FStar_Pervasives_Native.None)::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____11673, uu____11674) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown, uu____11707) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match (uu____11728, branches),
               uu____11730) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc ->
                        fun br ->
                          match acc with
                          | Yes uu____11794 -> Maybe
                          | Maybe -> Maybe
                          | No ->
                              let uu____11795 =
                                FStar_Syntax_Subst.open_branch br in
                              (match uu____11795 with
                               | (uu____11796, uu____11797, br_body) ->
                                   let uu____11815 =
                                     let uu____11816 =
                                       let uu____11821 =
                                         let uu____11822 =
                                           let uu____11825 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names in
                                           FStar_All.pipe_right uu____11825
                                             FStar_Util.set_elements in
                                         FStar_All.pipe_right uu____11822
                                           (FStar_TypeChecker_Env.push_bvs
                                              env) in
                                       check_erased uu____11821 in
                                     FStar_All.pipe_right br_body uu____11816 in
                                   (match uu____11815 with
                                    | No -> No
                                    | uu____11836 -> Maybe))) No)
            | uu____11837 -> No in
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
            (((let uu____11889 = FStar_Options.use_two_phase_tc () in
               Prims.op_Negation uu____11889) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ()) in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
               let uu____11908 =
                 let uu____11909 = FStar_Syntax_Subst.compress t1 in
                 uu____11909.FStar_Syntax_Syntax.n in
               match uu____11908 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____11914 -> false in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
               let uu____11924 =
                 let uu____11925 = FStar_Syntax_Subst.compress t1 in
                 uu____11925.FStar_Syntax_Syntax.n in
               match uu____11924 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____11930 -> false in
             let is_type t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
               let t2 = FStar_Syntax_Util.unrefine t1 in
               let uu____11941 =
                 let uu____11942 = FStar_Syntax_Subst.compress t2 in
                 uu____11942.FStar_Syntax_Syntax.n in
               match uu____11941 with
               | FStar_Syntax_Syntax.Tm_type uu____11946 -> true
               | uu____11948 -> false in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ in
             let uu____11951 = FStar_Syntax_Util.head_and_args res_typ in
             match uu____11951 with
             | (head, args) ->
                 ((let uu____12001 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions") in
                   if uu____12001
                   then
                     let uu____12005 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                     let uu____12007 = FStar_Syntax_Print.term_to_string e in
                     let uu____12009 =
                       FStar_Syntax_Print.term_to_string res_typ in
                     let uu____12011 =
                       FStar_Syntax_Print.term_to_string exp_t in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____12005 uu____12007 uu____12009 uu____12011
                   else ());
                  (let mk_erased u t =
                     let uu____12029 =
                       let uu____12032 =
                         fvar_const env FStar_Parser_Const.erased_lid in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____12032 [u] in
                     let uu____12033 =
                       let uu____12044 = FStar_Syntax_Syntax.as_arg t in
                       [uu____12044] in
                     FStar_Syntax_Util.mk_app uu____12029 uu____12033 in
                   let uu____12069 =
                     let uu____12084 =
                       let uu____12085 = FStar_Syntax_Util.un_uinst head in
                       uu____12085.FStar_Syntax_Syntax.n in
                     (uu____12084, args) in
                   match uu____12069 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type exp_t)
                       ->
                       let uu____12123 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total in
                       (match uu____12123 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____12163 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac in
                       (match uu____12163 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____12203 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac in
                       (match uu____12203 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____12243 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac in
                       (match uu____12243 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____12264 ->
                       let uu____12279 =
                         let uu____12284 = check_erased env res_typ in
                         let uu____12285 = check_erased env exp_t in
                         (uu____12284, uu____12285) in
                       (match uu____12279 with
                        | (No, Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty in
                            let uu____12294 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty in
                            (match uu____12294 with
                             | FStar_Pervasives_Native.None ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e in
                                 let uu____12305 =
                                   let uu____12310 =
                                     let uu____12311 =
                                       FStar_Syntax_Syntax.iarg ty in
                                     [uu____12311] in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____12310
                                     FStar_Syntax_Syntax.mk_Total in
                                 (match uu____12305 with
                                  | (e1, lc1) -> (e1, lc1, g1)))
                        | (Yes ty, No) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty in
                            let uu____12346 =
                              let uu____12351 =
                                let uu____12352 = FStar_Syntax_Syntax.iarg ty in
                                [uu____12352] in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____12351
                                FStar_Syntax_Syntax.mk_GTotal in
                            (match uu____12346 with
                             | (e1, lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____12385 ->
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
        let uu____12420 = FStar_Syntax_Util.head_and_args rt1 in
        match uu____12420 with
        | (hd, args) ->
            let uu____12469 =
              let uu____12484 =
                let uu____12485 = FStar_Syntax_Subst.compress hd in
                uu____12485.FStar_Syntax_Syntax.n in
              (uu____12484, args) in
            (match uu____12469 with
             | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____12523 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac in
                 FStar_All.pipe_left
                   (fun uu____12550 ->
                      FStar_Pervasives_Native.Some uu____12550) uu____12523
             | uu____12551 -> FStar_Pervasives_Native.None)
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
          (let uu____12604 =
             FStar_TypeChecker_Env.debug env FStar_Options.High in
           if uu____12604
           then
             let uu____12607 = FStar_Syntax_Print.term_to_string e in
             let uu____12609 = FStar_TypeChecker_Common.lcomp_to_string lc in
             let uu____12611 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____12607 uu____12609 uu____12611
           else ());
          (let use_eq =
             (env.FStar_TypeChecker_Env.use_eq_strict ||
                env.FStar_TypeChecker_Env.use_eq)
               ||
               (let uu____12621 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name in
                match uu____12621 with
                | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____12646 -> false) in
           let gopt =
             if use_eq
             then
               let uu____12672 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t in
               (uu____12672, false)
             else
               (let uu____12682 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t in
                (uu____12682, true)) in
           match gopt with
           | (FStar_Pervasives_Native.None, uu____12695) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____12707 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ in
                 FStar_Errors.raise_error uu____12707
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1419_12723 = lc in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1419_12723.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1419_12723.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1419_12723.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g, apply_guard) ->
               let uu____12730 = FStar_TypeChecker_Env.guard_form g in
               (match uu____12730 with
                | FStar_TypeChecker_Common.Trivial ->
                    let strengthen_trivial uu____12746 =
                      let uu____12747 =
                        FStar_TypeChecker_Common.lcomp_comp lc in
                      match uu____12747 with
                      | (c, g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c in
                          let set_result_typ c1 =
                            FStar_Syntax_Util.set_result_typ c1 t in
                          let uu____12767 =
                            let uu____12769 = FStar_Syntax_Util.eq_tm t res_t in
                            uu____12769 = FStar_Syntax_Util.Equal in
                          if uu____12767
                          then
                            ((let uu____12776 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____12776
                              then
                                let uu____12780 =
                                  FStar_Syntax_Print.term_to_string res_t in
                                let uu____12782 =
                                  FStar_Syntax_Print.term_to_string t in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____12780 uu____12782
                              else ());
                             (let uu____12787 = set_result_typ c in
                              (uu____12787, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____12794 ->
                                   true
                               | uu____12802 -> false in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t in
                               let uu____12810 =
                                 let uu____12815 =
                                   let uu____12816 =
                                     FStar_All.pipe_right c
                                       FStar_Syntax_Util.comp_effect_name in
                                   FStar_All.pipe_right uu____12816
                                     (FStar_TypeChecker_Env.norm_eff_name env) in
                                 let uu____12819 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env uu____12815
                                   (comp_univ_opt c) res_t uu____12819 in
                               match uu____12810 with
                               | (cret, gret) ->
                                   let lc1 =
                                     let uu____12829 =
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                         c in
                                     let uu____12830 =
                                       let uu____12831 =
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                           cret in
                                       ((FStar_Pervasives_Native.Some x),
                                         uu____12831) in
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (FStar_Pervasives_Native.Some e)
                                       uu____12829 uu____12830 in
                                   ((let uu____12835 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme in
                                     if uu____12835
                                     then
                                       let uu____12839 =
                                         FStar_Syntax_Print.term_to_string e in
                                       let uu____12841 =
                                         FStar_Syntax_Print.comp_to_string c in
                                       let uu____12843 =
                                         FStar_Syntax_Print.term_to_string t in
                                       let uu____12845 =
                                         FStar_TypeChecker_Common.lcomp_to_string
                                           lc1 in
                                       FStar_Util.print4
                                         "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                         uu____12839 uu____12841 uu____12843
                                         uu____12845
                                     else ());
                                    (let uu____12850 =
                                       FStar_TypeChecker_Common.lcomp_comp
                                         lc1 in
                                     match uu____12850 with
                                     | (c1, g_lc) ->
                                         let uu____12861 = set_result_typ c1 in
                                         let uu____12862 =
                                           FStar_TypeChecker_Env.conj_guards
                                             [g_c; gret; g_lc] in
                                         (uu____12861, uu____12862)))
                             else
                               ((let uu____12866 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____12866
                                 then
                                   let uu____12870 =
                                     FStar_Syntax_Print.term_to_string res_t in
                                   let uu____12872 =
                                     FStar_Syntax_Print.comp_to_string c in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____12870 uu____12872
                                 else ());
                                (let uu____12877 = set_result_typ c in
                                 (uu____12877, g_c)))) in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1458_12881 = g in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred_to_tac =
                          (uu___1458_12881.FStar_TypeChecker_Common.deferred_to_tac);
                        FStar_TypeChecker_Common.deferred =
                          (uu___1458_12881.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1458_12881.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1458_12881.FStar_TypeChecker_Common.implicits)
                      } in
                    let strengthen uu____12891 =
                      let uu____12892 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ()) in
                      if uu____12892
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f in
                         let uu____12902 =
                           let uu____12903 = FStar_Syntax_Subst.compress f1 in
                           uu____12903.FStar_Syntax_Syntax.n in
                         match uu____12902 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____12910,
                              {
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Tm_fvar fv;
                                FStar_Syntax_Syntax.pos = uu____12912;
                                FStar_Syntax_Syntax.vars = uu____12913;_},
                              uu____12914)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1474_12940 = lc in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1474_12940.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1474_12940.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1474_12940.FStar_TypeChecker_Common.comp_thunk)
                               } in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____12941 ->
                             let uu____12942 =
                               FStar_TypeChecker_Common.lcomp_comp lc in
                             (match uu____12942 with
                              | (c, g_c) ->
                                  ((let uu____12954 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme in
                                    if uu____12954
                                    then
                                      let uu____12958 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ in
                                      let uu____12960 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t in
                                      let uu____12962 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c in
                                      let uu____12964 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1 in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____12958 uu____12960 uu____12962
                                        uu____12964
                                    else ());
                                   (let u_t_opt = comp_univ_opt c in
                                    let x =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (t.FStar_Syntax_Syntax.pos)) t in
                                    let xexp =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____12974 =
                                      let uu____12979 =
                                        let uu____12980 =
                                          FStar_All.pipe_right c
                                            FStar_Syntax_Util.comp_effect_name in
                                        FStar_All.pipe_right uu____12980
                                          (FStar_TypeChecker_Env.norm_eff_name
                                             env) in
                                      return_value env uu____12979 u_t_opt t
                                        xexp in
                                    match uu____12974 with
                                    | (cret, gret) ->
                                        let guard =
                                          if apply_guard
                                          then
                                            let uu____12991 =
                                              let uu____12992 =
                                                FStar_Syntax_Syntax.as_arg
                                                  xexp in
                                              [uu____12992] in
                                            FStar_Syntax_Syntax.mk_Tm_app f1
                                              uu____12991
                                              f1.FStar_Syntax_Syntax.pos
                                          else f1 in
                                        let uu____13019 =
                                          let uu____13024 =
                                            FStar_All.pipe_left
                                              (fun uu____13045 ->
                                                 FStar_Pervasives_Native.Some
                                                   uu____13045)
                                              (FStar_TypeChecker_Err.subtyping_failed
                                                 env
                                                 lc.FStar_TypeChecker_Common.res_typ
                                                 t) in
                                          let uu____13046 =
                                            let uu____13047 =
                                              FStar_TypeChecker_Env.push_bvs
                                                env [x] in
                                            FStar_TypeChecker_Env.set_range
                                              uu____13047
                                              e.FStar_Syntax_Syntax.pos in
                                          let uu____13048 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              cret in
                                          let uu____13049 =
                                            FStar_All.pipe_left
                                              FStar_TypeChecker_Env.guard_of_guard_formula
                                              (FStar_TypeChecker_Common.NonTrivial
                                                 guard) in
                                          strengthen_precondition uu____13024
                                            uu____13046 e uu____13048
                                            uu____13049 in
                                        (match uu____13019 with
                                         | (eq_ret,
                                            _trivial_so_ok_to_discard) ->
                                             let x1 =
                                               let uu___1494_13057 = x in
                                               {
                                                 FStar_Syntax_Syntax.ppname =
                                                   (uu___1494_13057.FStar_Syntax_Syntax.ppname);
                                                 FStar_Syntax_Syntax.index =
                                                   (uu___1494_13057.FStar_Syntax_Syntax.index);
                                                 FStar_Syntax_Syntax.sort =
                                                   (lc.FStar_TypeChecker_Common.res_typ)
                                               } in
                                             let c1 =
                                               let uu____13059 =
                                                 FStar_TypeChecker_Common.lcomp_of_comp
                                                   c in
                                               bind e.FStar_Syntax_Syntax.pos
                                                 env
                                                 (FStar_Pervasives_Native.Some
                                                    e) uu____13059
                                                 ((FStar_Pervasives_Native.Some
                                                     x1), eq_ret) in
                                             let uu____13062 =
                                               FStar_TypeChecker_Common.lcomp_comp
                                                 c1 in
                                             (match uu____13062 with
                                              | (c2, g_lc) ->
                                                  ((let uu____13074 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        FStar_Options.Extreme in
                                                    if uu____13074
                                                    then
                                                      let uu____13078 =
                                                        FStar_TypeChecker_Normalize.comp_to_string
                                                          env c2 in
                                                      FStar_Util.print1
                                                        "Strengthened to %s\n"
                                                        uu____13078
                                                    else ());
                                                   (let uu____13083 =
                                                      FStar_TypeChecker_Env.conj_guards
                                                        [g_c; gret; g_lc] in
                                                    (c2, uu____13083))))))))) in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_13092 ->
                              match uu___6_13092 with
                              | FStar_Syntax_Syntax.RETURN ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____13095 -> [])) in
                    let lc1 =
                      let uu____13097 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name in
                      FStar_TypeChecker_Common.mk_lcomp uu____13097 t flags
                        strengthen in
                    let g2 =
                      let uu___1510_13099 = g1 in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred_to_tac =
                          (uu___1510_13099.FStar_TypeChecker_Common.deferred_to_tac);
                        FStar_TypeChecker_Common.deferred =
                          (uu___1510_13099.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1510_13099.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1510_13099.FStar_TypeChecker_Common.implicits)
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
        let uu____13135 =
          let uu____13138 =
            let uu____13139 =
              let uu____13148 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_Syntax_Syntax.as_arg uu____13148 in
            [uu____13139] in
          FStar_Syntax_Syntax.mk_Tm_app ens uu____13138
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____13135 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t in
      let uu____13171 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____13171
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____13190 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____13206 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____13223 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid) in
             if uu____13223
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req, uu____13239)::(ens, uu____13241)::uu____13242 ->
                    let uu____13285 =
                      let uu____13288 = norm req in
                      FStar_Pervasives_Native.Some uu____13288 in
                    let uu____13289 =
                      let uu____13290 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____13290 in
                    (uu____13285, uu____13289)
                | uu____13293 ->
                    let uu____13304 =
                      let uu____13310 =
                        let uu____13312 =
                          FStar_Syntax_Print.comp_to_string comp in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____13312 in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____13310) in
                    FStar_Errors.raise_error uu____13304
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp, uu____13332)::uu____13333 ->
                    let uu____13360 =
                      let uu____13365 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____13365 in
                    (match uu____13360 with
                     | (us_r, uu____13397) ->
                         let uu____13398 =
                           let uu____13403 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____13403 in
                         (match uu____13398 with
                          | (us_e, uu____13435) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____13438 =
                                  let uu____13439 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r in
                                  FStar_Syntax_Syntax.fvar uu____13439
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____13438
                                  us_r in
                              let as_ens =
                                let uu____13441 =
                                  let uu____13442 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r in
                                  FStar_Syntax_Syntax.fvar uu____13442
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____13441
                                  us_e in
                              let req =
                                let uu____13444 =
                                  let uu____13445 =
                                    let uu____13456 =
                                      FStar_Syntax_Syntax.as_arg wp in
                                    [uu____13456] in
                                  ((ct1.FStar_Syntax_Syntax.result_typ),
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.imp_tag))
                                    :: uu____13445 in
                                FStar_Syntax_Syntax.mk_Tm_app as_req
                                  uu____13444
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____13494 =
                                  let uu____13495 =
                                    let uu____13506 =
                                      FStar_Syntax_Syntax.as_arg wp in
                                    [uu____13506] in
                                  ((ct1.FStar_Syntax_Syntax.result_typ),
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.imp_tag))
                                    :: uu____13495 in
                                FStar_Syntax_Syntax.mk_Tm_app as_ens
                                  uu____13494
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____13543 =
                                let uu____13546 = norm req in
                                FStar_Pervasives_Native.Some uu____13546 in
                              let uu____13547 =
                                let uu____13548 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____13548 in
                              (uu____13543, uu____13547)))
                | uu____13551 -> failwith "Impossible"))
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
        (let uu____13590 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____13590
         then
           let uu____13595 = FStar_Syntax_Print.term_to_string tm in
           let uu____13597 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____13595
             uu____13597
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
          (let uu____13656 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify") in
           if uu____13656
           then
             let uu____13661 = FStar_Syntax_Print.term_to_string tm in
             let uu____13663 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____13661
               uu____13663
           else ());
          tm'
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____13674 =
      let uu____13676 =
        let uu____13677 = FStar_Syntax_Subst.compress t in
        uu____13677.FStar_Syntax_Syntax.n in
      match uu____13676 with
      | FStar_Syntax_Syntax.Tm_app uu____13681 -> false
      | uu____13699 -> true in
    if uu____13674
    then t
    else
      (let uu____13704 = FStar_Syntax_Util.head_and_args t in
       match uu____13704 with
       | (head, args) ->
           let uu____13747 =
             let uu____13749 =
               let uu____13750 = FStar_Syntax_Subst.compress head in
               uu____13750.FStar_Syntax_Syntax.n in
             match uu____13749 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) ->
                 true
             | uu____13755 -> false in
           if uu____13747
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____13787 ->
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
          ((let uu____13834 =
              FStar_TypeChecker_Env.debug env FStar_Options.High in
            if uu____13834
            then
              let uu____13837 = FStar_Syntax_Print.term_to_string e in
              let uu____13839 = FStar_Syntax_Print.term_to_string t in
              let uu____13841 =
                let uu____13843 = FStar_TypeChecker_Env.expected_typ env in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____13843 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____13837 uu____13839 uu____13841
            else ());
           (let unfolded_arrow_formals t1 =
              let rec aux bs t2 =
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf env t2 in
                let uu____13879 = FStar_Syntax_Util.arrow_formals t3 in
                match uu____13879 with
                | (bs', t4) ->
                    (match bs' with
                     | [] -> bs
                     | bs'1 -> aux (FStar_List.append bs bs'1) t4) in
              aux [] t1 in
            let number_of_implicits t1 =
              let formals = unfolded_arrow_formals t1 in
              let n_implicits =
                let uu____13913 =
                  FStar_All.pipe_right formals
                    (FStar_Util.prefix_until
                       (fun uu____13991 ->
                          match uu____13991 with
                          | (uu____13999, imp) ->
                              (FStar_Option.isNone imp) ||
                                (let uu____14006 =
                                   FStar_Syntax_Util.eq_aqual imp
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Equality) in
                                 uu____14006 = FStar_Syntax_Util.Equal))) in
                match uu____13913 with
                | FStar_Pervasives_Native.None -> FStar_List.length formals
                | FStar_Pervasives_Native.Some
                    (implicits, _first_explicit, _rest) ->
                    FStar_List.length implicits in
              n_implicits in
            let inst_n_binders t1 =
              let uu____14125 = FStar_TypeChecker_Env.expected_typ env in
              match uu____14125 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t in
                  let n_available = number_of_implicits t1 in
                  if n_available < n_expected
                  then
                    let uu____14139 =
                      let uu____14145 =
                        let uu____14147 = FStar_Util.string_of_int n_expected in
                        let uu____14149 = FStar_Syntax_Print.term_to_string e in
                        let uu____14151 =
                          FStar_Util.string_of_int n_available in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____14147 uu____14149 uu____14151 in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____14145) in
                    let uu____14155 = FStar_TypeChecker_Env.get_range env in
                    FStar_Errors.raise_error uu____14139 uu____14155
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected) in
            let decr_inst uu___7_14173 =
              match uu___7_14173 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one) in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                let uu____14216 = FStar_Syntax_Subst.open_comp bs c in
                (match uu____14216 with
                 | (bs1, c1) ->
                     let rec aux subst inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some uu____14347,
                          uu____14334) when uu____14347 = Prims.int_zero ->
                           ([], bs2, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____14380,
                          (x, FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit uu____14382))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort in
                           let uu____14416 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2 in
                           (match uu____14416 with
                            | (v, uu____14457, g) ->
                                ((let uu____14472 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High in
                                  if uu____14472
                                  then
                                    let uu____14475 =
                                      FStar_Syntax_Print.term_to_string v in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____14475
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst in
                                  let uu____14485 =
                                    aux subst1 (decr_inst inst_n) rest in
                                  match uu____14485 with
                                  | (args, bs3, subst2, g') ->
                                      let uu____14578 =
                                        FStar_TypeChecker_Env.conj_guard g g' in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____14578))))
                       | (uu____14605,
                          (x, FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tac_or_attr))::rest) ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort in
                           let meta_t =
                             match tac_or_attr with
                             | FStar_Syntax_Syntax.Arg_qualifier_meta_tac tau
                                 ->
                                 let uu____14644 =
                                   let uu____14651 = FStar_Dyn.mkdyn env in
                                   (uu____14651, tau) in
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   uu____14644
                             | FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                 attr ->
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_attr attr in
                           let uu____14657 =
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict
                               (FStar_Pervasives_Native.Some meta_t) in
                           (match uu____14657 with
                            | (v, uu____14698, g) ->
                                ((let uu____14713 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High in
                                  if uu____14713
                                  then
                                    let uu____14716 =
                                      FStar_Syntax_Print.term_to_string v in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____14716
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst in
                                  let uu____14726 =
                                    aux subst1 (decr_inst inst_n) rest in
                                  match uu____14726 with
                                  | (args, bs3, subst2, g') ->
                                      let uu____14819 =
                                        FStar_TypeChecker_Env.conj_guard g g' in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____14819))))
                       | (uu____14846, bs3) ->
                           ([], bs3, subst,
                             FStar_TypeChecker_Env.trivial_guard) in
                     let uu____14894 =
                       let uu____14921 = inst_n_binders t1 in
                       aux [] uu____14921 bs1 in
                     (match uu____14894 with
                      | (args, bs2, subst, guard) ->
                          (match (args, bs2) with
                           | ([], uu____14993) -> (e, torig, guard)
                           | (uu____15024, []) when
                               let uu____15055 =
                                 FStar_Syntax_Util.is_total_comp c1 in
                               Prims.op_Negation uu____15055 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____15057 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____15085 ->
                                     FStar_Syntax_Util.arrow bs2 c1 in
                               let t3 = FStar_Syntax_Subst.subst subst t2 in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   e.FStar_Syntax_Syntax.pos in
                               (e1, t3, guard))))
            | uu____15096 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs ->
    let uu____15108 =
      let uu____15112 = FStar_Util.set_elements univs in
      FStar_All.pipe_right uu____15112
        (FStar_List.map
           (fun u ->
              let uu____15124 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____15124 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____15108 (FStar_String.concat ", ")
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env ->
    fun x ->
      let uu____15152 = FStar_Util.set_is_empty x in
      if uu____15152
      then []
      else
        (let s =
           let uu____15172 =
             let uu____15175 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____15175 in
           FStar_All.pipe_right uu____15172 FStar_Util.set_elements in
         (let uu____15193 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____15193
          then
            let uu____15198 =
              let uu____15200 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____15200 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____15198
          else ());
         (let r =
            let uu____15209 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____15209 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____15254 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____15254
                     then
                       let uu____15259 =
                         let uu____15261 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____15261 in
                       let uu____15265 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____15267 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____15259 uu____15265 uu____15267
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
        let uu____15297 =
          FStar_Util.set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____15297 FStar_Util.set_elements in
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
        | ([], uu____15336) -> generalized_univ_names
        | (uu____15343, []) -> explicit_univ_names
        | uu____15350 ->
            let uu____15359 =
              let uu____15365 =
                let uu____15367 = FStar_Syntax_Print.term_to_string t in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____15367 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____15365) in
            FStar_Errors.raise_error uu____15359 t.FStar_Syntax_Syntax.pos
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
      (let uu____15389 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____15389
       then
         let uu____15394 = FStar_Syntax_Print.term_to_string t in
         let uu____15396 = FStar_Syntax_Print.univ_names_to_string univnames in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____15394 uu____15396
       else ());
      (let univs = FStar_Syntax_Free.univs t in
       (let uu____15405 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____15405
        then
          let uu____15410 = string_of_univs univs in
          FStar_Util.print1 "univs to gen : %s\n" uu____15410
        else ());
       (let gen = gen_univs env univs in
        (let uu____15419 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen") in
         if uu____15419
         then
           let uu____15424 = FStar_Syntax_Print.term_to_string t in
           let uu____15426 = FStar_Syntax_Print.univ_names_to_string gen in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____15424 uu____15426
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
        let uu____15510 =
          let uu____15512 =
            FStar_Util.for_all
              (fun uu____15526 ->
                 match uu____15526 with
                 | (uu____15536, uu____15537, c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          FStar_All.pipe_left Prims.op_Negation uu____15512 in
        if uu____15510
        then FStar_Pervasives_Native.None
        else
          (let norm c =
             (let uu____15589 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              if uu____15589
              then
                let uu____15592 = FStar_Syntax_Print.comp_to_string c in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____15592
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c in
              (let uu____15599 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____15599
               then
                 let uu____15602 = FStar_Syntax_Print.comp_to_string c1 in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____15602
               else ());
              c1) in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu____15620 = FStar_Util.set_difference uvs env_uvars in
             FStar_All.pipe_right uu____15620 FStar_Util.set_elements in
           let univs_and_uvars_of_lec uu____15654 =
             match uu____15654 with
             | (lbname, e, c) ->
                 let c1 = norm c in
                 let t = FStar_Syntax_Util.comp_result c1 in
                 let univs = FStar_Syntax_Free.univs t in
                 let uvt = FStar_Syntax_Free.uvars t in
                 ((let uu____15691 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen") in
                   if uu____15691
                   then
                     let uu____15696 =
                       let uu____15698 =
                         let uu____15702 = FStar_Util.set_elements univs in
                         FStar_All.pipe_right uu____15702
                           (FStar_List.map
                              (fun u ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u))) in
                       FStar_All.pipe_right uu____15698
                         (FStar_String.concat ", ") in
                     let uu____15758 =
                       let uu____15760 =
                         let uu____15764 = FStar_Util.set_elements uvt in
                         FStar_All.pipe_right uu____15764
                           (FStar_List.map
                              (fun u ->
                                 let uu____15777 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head in
                                 let uu____15779 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                 FStar_Util.format2 "(%s : %s)" uu____15777
                                   uu____15779)) in
                       FStar_All.pipe_right uu____15760
                         (FStar_String.concat ", ") in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____15696
                       uu____15758
                   else ());
                  (let univs1 =
                     let uu____15793 = FStar_Util.set_elements uvt in
                     FStar_List.fold_left
                       (fun univs1 ->
                          fun uv ->
                            let uu____15805 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ in
                            FStar_Util.set_union univs1 uu____15805) univs
                       uu____15793 in
                   let uvs = gen_uvars uvt in
                   (let uu____15812 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen") in
                    if uu____15812
                    then
                      let uu____15817 =
                        let uu____15819 =
                          let uu____15823 = FStar_Util.set_elements univs1 in
                          FStar_All.pipe_right uu____15823
                            (FStar_List.map
                               (fun u ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u))) in
                        FStar_All.pipe_right uu____15819
                          (FStar_String.concat ", ") in
                      let uu____15879 =
                        let uu____15881 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u ->
                                  let uu____15895 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head in
                                  let uu____15897 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                  FStar_Util.format2 "(%s : %s)" uu____15895
                                    uu____15897)) in
                        FStar_All.pipe_right uu____15881
                          (FStar_String.concat ", ") in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____15817 uu____15879
                    else ());
                   (univs1, uvs, (lbname, e, c1)))) in
           let uu____15918 =
             let uu____15935 = FStar_List.hd lecs in
             univs_and_uvars_of_lec uu____15935 in
           match uu____15918 with
           | (univs, uvs, lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____16025 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1) in
                 if uu____16025
                 then ()
                 else
                   (let uu____16030 = lec_hd in
                    match uu____16030 with
                    | (lb1, uu____16038, uu____16039) ->
                        let uu____16040 = lec2 in
                        (match uu____16040 with
                         | (lb2, uu____16048, uu____16049) ->
                             let msg =
                               let uu____16052 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____16054 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____16052 uu____16054 in
                             let uu____16057 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____16057)) in
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
                 let uu____16125 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1) in
                 if uu____16125
                 then ()
                 else
                   (let uu____16130 = lec_hd in
                    match uu____16130 with
                    | (lb1, uu____16138, uu____16139) ->
                        let uu____16140 = lec2 in
                        (match uu____16140 with
                         | (lb2, uu____16148, uu____16149) ->
                             let msg =
                               let uu____16152 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____16154 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____16152 uu____16154 in
                             let uu____16157 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____16157)) in
               let lecs1 =
                 let uu____16168 = FStar_List.tl lecs in
                 FStar_List.fold_right
                   (fun this_lec ->
                      fun lecs1 ->
                        let uu____16221 = univs_and_uvars_of_lec this_lec in
                        match uu____16221 with
                        | (this_univs, this_uvs, this_lec1) ->
                            (force_univs_eq this_lec1 univs this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____16168 [] in
               let lecs2 = lec_hd :: lecs1 in
               let gen_types uvs1 =
                 let fail rng k =
                   let uu____16331 = lec_hd in
                   match uu____16331 with
                   | (lbname, e, c) ->
                       let uu____16341 =
                         let uu____16347 =
                           let uu____16349 =
                             FStar_Syntax_Print.term_to_string k in
                           let uu____16351 =
                             FStar_Syntax_Print.lbname_to_string lbname in
                           let uu____16353 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c) in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____16349 uu____16351 uu____16353 in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____16347) in
                       FStar_Errors.raise_error uu____16341 rng in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u ->
                         let uu____16375 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head in
                         match uu____16375 with
                         | FStar_Pervasives_Native.Some uu____16384 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____16392 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ in
                             let uu____16396 =
                               FStar_Syntax_Util.arrow_formals k in
                             (match uu____16396 with
                              | (bs, kres) ->
                                  ((let uu____16416 =
                                      let uu____16417 =
                                        let uu____16420 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres in
                                        FStar_Syntax_Util.unrefine
                                          uu____16420 in
                                      uu____16417.FStar_Syntax_Syntax.n in
                                    match uu____16416 with
                                    | FStar_Syntax_Syntax.Tm_type uu____16421
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres in
                                        let uu____16425 =
                                          let uu____16427 =
                                            FStar_Util.set_is_empty free in
                                          Prims.op_Negation uu____16427 in
                                        if uu____16425
                                        then
                                          fail
                                            u.FStar_Syntax_Syntax.ctx_uvar_range
                                            kres
                                        else ()
                                    | uu____16432 ->
                                        fail
                                          u.FStar_Syntax_Syntax.ctx_uvar_range
                                          kres);
                                   (let a =
                                      let uu____16434 =
                                        let uu____16437 =
                                          FStar_TypeChecker_Env.get_range env in
                                        FStar_All.pipe_left
                                          (fun uu____16440 ->
                                             FStar_Pervasives_Native.Some
                                               uu____16440) uu____16437 in
                                      FStar_Syntax_Syntax.new_bv uu____16434
                                        kres in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____16448 ->
                                          let uu____16449 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Util.abs bs
                                            uu____16449
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
                      (fun uu____16552 ->
                         match uu____16552 with
                         | (lbname, e, c) ->
                             let uu____16598 =
                               match (gen_tvars, gen_univs1) with
                               | ([], []) -> (e, c, [])
                               | uu____16659 ->
                                   let uu____16672 = (e, c) in
                                   (match uu____16672 with
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
                                                (fun uu____16712 ->
                                                   match uu____16712 with
                                                   | (x, uu____16718) ->
                                                       let uu____16719 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____16719)
                                                gen_tvars in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____16737 =
                                                let uu____16739 =
                                                  FStar_Util.right lbname in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____16739 in
                                              if uu____16737
                                              then
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  tm tvar_args
                                                  tm.FStar_Syntax_Syntax.pos
                                              else tm in
                                            FStar_Syntax_InstFV.inst
                                              instantiate_lbname_with_app e1
                                          else e1 in
                                        let t =
                                          let uu____16748 =
                                            let uu____16749 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____16749.FStar_Syntax_Syntax.n in
                                          match uu____16748 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs, cod) ->
                                              let uu____16774 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____16774 with
                                               | (bs1, cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____16785 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____16789 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____16789, gen_tvars)) in
                             (match uu____16598 with
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
        (let uu____16936 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____16936
         then
           let uu____16939 =
             let uu____16941 =
               FStar_List.map
                 (fun uu____16956 ->
                    match uu____16956 with
                    | (lb, uu____16965, uu____16966) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_All.pipe_right uu____16941 (FStar_String.concat ", ") in
           FStar_Util.print1 "Generalizing: %s\n" uu____16939
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____16992 ->
                match uu____16992 with
                | (l, t, c) -> gather_free_univnames env t) lecs in
         let generalized_lecs =
           let uu____17021 = gen env is_rec lecs in
           match uu____17021 with
           | FStar_Pervasives_Native.None ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____17120 ->
                       match uu____17120 with
                       | (l, t, c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____17182 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 if uu____17182
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____17230 ->
                           match uu____17230 with
                           | (l, us, e, c, gvs) ->
                               let uu____17264 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos in
                               let uu____17266 =
                                 FStar_Syntax_Print.lbname_to_string l in
                               let uu____17268 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c) in
                               let uu____17270 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____17272 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____17264 uu____17266 uu____17268
                                 uu____17270 uu____17272))
                 else ());
                luecs) in
         FStar_List.map2
           (fun univnames ->
              fun uu____17317 ->
                match uu____17317 with
                | (l, generalized_univs, t, c, gvs) ->
                    let uu____17361 =
                      check_universe_generalization univnames
                        generalized_univs t in
                    (l, uu____17361, t, c, gvs)) univnames_lecs
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
        let uu____17416 =
          let uu____17420 =
            let uu____17422 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.string_of_lid uu____17422 in
          FStar_Pervasives_Native.Some uu____17420 in
        FStar_Profiling.profile
          (fun uu____17439 -> generalize' env is_rec lecs) uu____17416
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
              let uu____17496 =
                FStar_TypeChecker_Rel.teq_nosmt_force env2 t1 t21 in
              (if uu____17496
               then
                 FStar_All.pipe_right FStar_TypeChecker_Env.trivial_guard
                   (fun uu____17502 ->
                      FStar_Pervasives_Native.Some uu____17502)
               else FStar_Pervasives_Native.None)
            else
              if env2.FStar_TypeChecker_Env.use_eq
              then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
              else
                (let uu____17511 =
                   FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21 in
                 match uu____17511 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some f ->
                     let uu____17517 = FStar_TypeChecker_Env.apply_guard f e in
                     FStar_All.pipe_left
                       (fun uu____17520 ->
                          FStar_Pervasives_Native.Some uu____17520)
                       uu____17517) in
          let uu____17521 = maybe_coerce_lc env1 e lc t2 in
          match uu____17521 with
          | (e1, lc1, g_c) ->
              let uu____17537 =
                check env1 lc1.FStar_TypeChecker_Common.res_typ t2 in
              (match uu____17537 with
               | FStar_Pervasives_Native.None ->
                   let uu____17546 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ in
                   let uu____17552 = FStar_TypeChecker_Env.get_range env1 in
                   FStar_Errors.raise_error uu____17546 uu____17552
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____17561 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____17561
                     then
                       let uu____17566 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____17566
                     else ());
                    (let uu____17572 = FStar_TypeChecker_Env.conj_guard g g_c in
                     (e1, lc1, uu____17572))))
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env ->
    fun g ->
      fun lc ->
        (let uu____17600 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium in
         if uu____17600
         then
           let uu____17603 = FStar_TypeChecker_Common.lcomp_to_string lc in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____17603
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
         let uu____17617 = FStar_TypeChecker_Common.lcomp_comp lc in
         match uu____17617 with
         | (c, g_c) ->
             let uu____17629 = FStar_TypeChecker_Common.is_total_lcomp lc in
             if uu____17629
             then
               let uu____17637 =
                 let uu____17639 = FStar_TypeChecker_Env.conj_guard g1 g_c in
                 discharge uu____17639 in
               (uu____17637, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] in
                let c1 =
                  let uu____17647 =
                    let uu____17648 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    FStar_All.pipe_right uu____17648
                      FStar_Syntax_Syntax.mk_Comp in
                  FStar_All.pipe_right uu____17647
                    (FStar_TypeChecker_Normalize.normalize_comp steps env) in
                let uu____17649 = check_trivial_precondition env c1 in
                match uu____17649 with
                | (ct, vc, g_pre) ->
                    ((let uu____17665 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification") in
                      if uu____17665
                      then
                        let uu____17670 =
                          FStar_Syntax_Print.term_to_string vc in
                        FStar_Util.print1 "top-level VC: %s\n" uu____17670
                      else ());
                     (let uu____17675 =
                        let uu____17677 =
                          let uu____17678 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre in
                          FStar_TypeChecker_Env.conj_guard g1 uu____17678 in
                        discharge uu____17677 in
                      let uu____17679 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp in
                      (uu____17675, uu____17679)))))
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head ->
    fun seen_args ->
      let short_bin_op f uu___8_17713 =
        match uu___8_17713 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst, uu____17723)::[] -> f fst
        | uu____17748 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____17760 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____17760
          (fun uu____17761 -> FStar_TypeChecker_Common.NonTrivial uu____17761) in
      let op_or_e e =
        let uu____17772 =
          let uu____17773 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____17773 in
        FStar_All.pipe_right uu____17772
          (fun uu____17776 -> FStar_TypeChecker_Common.NonTrivial uu____17776) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun uu____17783 -> FStar_TypeChecker_Common.NonTrivial uu____17783) in
      let op_or_t t =
        let uu____17794 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____17794
          (fun uu____17797 -> FStar_TypeChecker_Common.NonTrivial uu____17797) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun uu____17804 -> FStar_TypeChecker_Common.NonTrivial uu____17804) in
      let short_op_ite uu___9_17810 =
        match uu___9_17810 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard, uu____17820)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard, uu____17847)::[] ->
            let uu____17888 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____17888
              (fun uu____17889 ->
                 FStar_TypeChecker_Common.NonTrivial uu____17889)
        | uu____17890 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____17902 =
          let uu____17910 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____17910) in
        let uu____17918 =
          let uu____17928 =
            let uu____17936 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____17936) in
          let uu____17944 =
            let uu____17954 =
              let uu____17962 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____17962) in
            let uu____17970 =
              let uu____17980 =
                let uu____17988 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____17988) in
              let uu____17996 =
                let uu____18006 =
                  let uu____18014 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____18014) in
                [uu____18006; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____17980 :: uu____17996 in
            uu____17954 :: uu____17970 in
          uu____17928 :: uu____17944 in
        uu____17902 :: uu____17918 in
      match head.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____18076 =
            FStar_Util.find_map table
              (fun uu____18091 ->
                 match uu____18091 with
                 | (x, mk) ->
                     let uu____18108 = FStar_Ident.lid_equals x lid in
                     if uu____18108
                     then
                       let uu____18113 = mk seen_args in
                       FStar_Pervasives_Native.Some uu____18113
                     else FStar_Pervasives_Native.None) in
          (match uu____18076 with
           | FStar_Pervasives_Native.None -> FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____18117 -> FStar_TypeChecker_Common.Trivial
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l ->
    let uu____18125 =
      let uu____18126 = FStar_Syntax_Util.un_uinst l in
      uu____18126.FStar_Syntax_Syntax.n in
    match uu____18125 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____18131 -> false
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env ->
    fun bs ->
      let pos bs1 =
        match bs1 with
        | (hd, uu____18167)::uu____18168 ->
            FStar_Syntax_Syntax.range_of_bv hd
        | uu____18187 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____18196, FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____18197))::uu____18198 -> bs
      | uu____18216 ->
          let uu____18217 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____18217 with
           | FStar_Pervasives_Native.None -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____18221 =
                 let uu____18222 = FStar_Syntax_Subst.compress t in
                 uu____18222.FStar_Syntax_Syntax.n in
               (match uu____18221 with
                | FStar_Syntax_Syntax.Tm_arrow (bs', uu____18226) ->
                    let uu____18247 =
                      FStar_Util.prefix_until
                        (fun uu___10_18287 ->
                           match uu___10_18287 with
                           | (uu____18295, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____18296)) ->
                               false
                           | uu____18301 -> true) bs' in
                    (match uu____18247 with
                     | FStar_Pervasives_Native.None -> bs
                     | FStar_Pervasives_Native.Some
                         ([], uu____18337, uu____18338) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps, uu____18410, uu____18411) ->
                         let uu____18484 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____18505 ->
                                   match uu____18505 with
                                   | (x, uu____18514) ->
                                       let uu____18519 =
                                         FStar_Ident.string_of_id
                                           x.FStar_Syntax_Syntax.ppname in
                                       FStar_Util.starts_with uu____18519 "'")) in
                         if uu____18484
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____18565 ->
                                     match uu____18565 with
                                     | (x, i) ->
                                         let uu____18584 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____18584, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____18595 -> bs))
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
            let uu____18624 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1)) in
            if uu____18624
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
          let uu____18655 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____18655
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
        (let uu____18698 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____18698
         then
           ((let uu____18703 = FStar_Ident.string_of_lid lident in
             d uu____18703);
            (let uu____18705 = FStar_Ident.string_of_lid lident in
             let uu____18707 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____18705 uu____18707))
         else ());
        (let fv =
           let uu____18713 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____18713
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
         let uu____18725 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Range.dummyRange in
         ((let uu___2136_18727 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2136_18727.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2136_18727.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2136_18727.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2136_18727.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2136_18727.FStar_Syntax_Syntax.sigopts)
           }), uu____18725))
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env ->
    fun se ->
      let visibility uu___11_18745 =
        match uu___11_18745 with
        | FStar_Syntax_Syntax.Private -> true
        | uu____18748 -> false in
      let reducibility uu___12_18756 =
        match uu___12_18756 with
        | FStar_Syntax_Syntax.Abstract -> true
        | FStar_Syntax_Syntax.Irreducible -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> true
        | FStar_Syntax_Syntax.Visible_default -> true
        | FStar_Syntax_Syntax.Inline_for_extraction -> true
        | uu____18763 -> false in
      let assumption uu___13_18771 =
        match uu___13_18771 with
        | FStar_Syntax_Syntax.Assumption -> true
        | FStar_Syntax_Syntax.New -> true
        | uu____18775 -> false in
      let reification uu___14_18783 =
        match uu___14_18783 with
        | FStar_Syntax_Syntax.Reifiable -> true
        | FStar_Syntax_Syntax.Reflectable uu____18786 -> true
        | uu____18788 -> false in
      let inferred uu___15_18796 =
        match uu___15_18796 with
        | FStar_Syntax_Syntax.Discriminator uu____18798 -> true
        | FStar_Syntax_Syntax.Projector uu____18800 -> true
        | FStar_Syntax_Syntax.RecordType uu____18806 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____18816 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor -> true
        | FStar_Syntax_Syntax.HasMaskedEffect -> true
        | FStar_Syntax_Syntax.Effect -> true
        | uu____18829 -> false in
      let has_eq uu___16_18837 =
        match uu___16_18837 with
        | FStar_Syntax_Syntax.Noeq -> true
        | FStar_Syntax_Syntax.Unopteq -> true
        | uu____18841 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____18920 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private -> true
        | uu____18927 -> true in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1 in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l ->
                  let uu____18960 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l in
                  FStar_Option.isSome uu____18960)) in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____18991 = FStar_Option.get attrs_opt in
                     FStar_Syntax_Util.has_attribute uu____18991
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
           | FStar_Syntax_Syntax.Sig_bundle uu____19011 ->
               let uu____19020 =
                 let uu____19022 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_19028 ->
                           match uu___17_19028 with
                           | FStar_Syntax_Syntax.Noeq -> true
                           | uu____19031 -> false)) in
                 Prims.op_Negation uu____19022 in
               if uu____19020
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____19038 -> ()
           | FStar_Syntax_Syntax.Sig_fail uu____19045 -> ()
           | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu____19059) ->
               let uu____19068 =
                 FStar_Syntax_Util.abs_formals lb.FStar_Syntax_Syntax.lbdef in
               (match uu____19068 with
                | (uu____19077, body, uu____19079) ->
                    let uu____19084 =
                      let uu____19086 =
                        FStar_TypeChecker_Normalize.non_info_norm env body in
                      Prims.op_Negation uu____19086 in
                    if uu____19084
                    then
                      let uu____19089 =
                        let uu____19095 =
                          let uu____19097 =
                            FStar_Syntax_Print.term_to_string body in
                          FStar_Util.format1
                            "Illegal attribute: the `erasable` attribute is only permitted on inductive type definitions and abbreviations for non-informative types. %s is considered informative."
                            uu____19097 in
                        (FStar_Errors.Fatal_QulifierListNotPermitted,
                          uu____19095) in
                      FStar_Errors.raise_error uu____19089
                        body.FStar_Syntax_Syntax.pos
                    else ())
           | uu____19103 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_QulifierListNotPermitted,
                   "Illegal attribute: the `erasable` attribute is only permitted on inductive type definitions and abbreviations for non-informative types")
                 r)
        else () in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic))) in
      let uu____19117 =
        let uu____19119 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_19125 ->
                  match uu___18_19125 with
                  | FStar_Syntax_Syntax.OnlyName -> true
                  | uu____19128 -> false)) in
        FStar_All.pipe_right uu____19119 Prims.op_Negation in
      if uu____19117
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x -> fun y -> x = y) quals in
        let err' msg =
          let uu____19149 =
            let uu____19155 =
              let uu____19157 = FStar_Syntax_Print.quals_to_string quals in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____19157 msg in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____19155) in
          FStar_Errors.raise_error uu____19149 r in
        let err msg = err' (Prims.op_Hat ": " msg) in
        let err'1 uu____19175 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____19183 =
            let uu____19185 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____19185 in
          if uu____19183 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec, uu____19196), uu____19197)
              ->
              ((let uu____19209 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____19209
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____19218 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x -> (assumption x) || (has_eq x))) in
                if uu____19218
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____19229 ->
              ((let uu____19239 =
                  let uu____19241 =
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
                  Prims.op_Negation uu____19241 in
                if uu____19239 then err'1 () else ());
               (let uu____19251 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_19257 ->
                           match uu___19_19257 with
                           | FStar_Syntax_Syntax.Unopteq -> true
                           | uu____19260 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr) in
                if uu____19251
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____19266 ->
              let uu____19273 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____19273 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____19281 ->
              let uu____19288 =
                let uu____19290 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____19290 in
              if uu____19288 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____19300 ->
              let uu____19301 =
                let uu____19303 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____19303 in
              if uu____19301 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19313 ->
              let uu____19326 =
                let uu____19328 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____19328 in
              if uu____19326 then err'1 () else ()
          | uu____19338 -> ()))
      else ()
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g ->
    fun t ->
      let rec descend env t1 =
        let uu____19377 =
          let uu____19378 = FStar_Syntax_Subst.compress t1 in
          uu____19378.FStar_Syntax_Syntax.n in
        match uu____19377 with
        | FStar_Syntax_Syntax.Tm_arrow uu____19382 ->
            let uu____19397 = FStar_Syntax_Util.arrow_formals_comp t1 in
            (match uu____19397 with
             | (bs, c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____19406;
               FStar_Syntax_Syntax.index = uu____19407;
               FStar_Syntax_Syntax.sort = t2;_},
             uu____19409)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head, uu____19418) -> descend env head
        | FStar_Syntax_Syntax.Tm_uinst (head, uu____19444) ->
            descend env head
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____19450 -> false
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
        (let uu____19460 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction") in
         if uu____19460
         then
           let uu____19465 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____19465
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
                  let uu____19530 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t in
                  FStar_Errors.raise_error uu____19530 r in
                let uu____19540 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts in
                match uu____19540 with
                | (uu____19549, signature) ->
                    let uu____19551 =
                      let uu____19552 = FStar_Syntax_Subst.compress signature in
                      uu____19552.FStar_Syntax_Syntax.n in
                    (match uu____19551 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs, uu____19560) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____19608 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b ->
                                     let uu____19624 =
                                       FStar_Syntax_Print.binder_to_string b in
                                     let uu____19626 =
                                       FStar_Ident.string_of_lid eff_name in
                                     let uu____19628 =
                                       FStar_Range.string_of_range r in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____19624 uu____19626 uu____19628) r in
                              (match uu____19608 with
                               | (is, g) ->
                                   let uu____19641 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None ->
                                         let eff_c =
                                           let uu____19643 =
                                             let uu____19644 =
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
                                                 = uu____19644;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____19643 in
                                         let uu____19663 =
                                           let uu____19664 =
                                             let uu____19679 =
                                               let uu____19688 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   FStar_Syntax_Syntax.t_unit in
                                               [uu____19688] in
                                             (uu____19679, eff_c) in
                                           FStar_Syntax_Syntax.Tm_arrow
                                             uu____19664 in
                                         FStar_Syntax_Syntax.mk uu____19663 r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____19719 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u] in
                                           FStar_All.pipe_right uu____19719
                                             FStar_Pervasives_Native.snd in
                                         let is_args =
                                           FStar_List.map2
                                             (fun i ->
                                                fun uu____19754 ->
                                                  match uu____19754 with
                                                  | (uu____19767, aqual) ->
                                                      (i, aqual)) is bs2 in
                                         let uu____19775 =
                                           let uu____19776 =
                                             FStar_Syntax_Syntax.as_arg a_tm in
                                           uu____19776 :: is_args in
                                         FStar_Syntax_Syntax.mk_Tm_app repr
                                           uu____19775 r in
                                   (uu____19641, g))
                          | uu____19789 -> fail signature)
                     | uu____19790 -> fail signature)
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
            let uu____19821 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env) in
            FStar_All.pipe_right uu____19821
              (fun ed ->
                 let uu____19829 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____19829 u a_tm)
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
              let uu____19865 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u] in
              match uu____19865 with
              | (uu____19870, sig_tm) ->
                  let fail t =
                    let uu____19878 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t in
                    FStar_Errors.raise_error uu____19878 r in
                  let uu____19884 =
                    let uu____19885 = FStar_Syntax_Subst.compress sig_tm in
                    uu____19885.FStar_Syntax_Syntax.n in
                  (match uu____19884 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs, uu____19889) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs in
                       (match bs1 with
                        | (a', uu____19912)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____19934 -> fail sig_tm)
                   | uu____19935 -> fail sig_tm)
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
          (let uu____19966 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects") in
           if uu____19966
           then
             let uu____19971 = FStar_Syntax_Print.comp_to_string c in
             let uu____19973 = FStar_Syntax_Print.lid_to_string tgt in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____19971 uu____19973
           else ());
          (let r = FStar_TypeChecker_Env.get_range env in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c in
           let lift_name =
             let uu____19982 =
               FStar_Ident.string_of_lid ct.FStar_Syntax_Syntax.effect_name in
             let uu____19984 = FStar_Ident.string_of_lid tgt in
             FStar_Util.format2 "%s ~> %s" uu____19982 uu____19984 in
           let uu____19987 =
             let uu____19998 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs in
             let uu____19999 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst) in
             (uu____19998, (ct.FStar_Syntax_Syntax.result_typ), uu____19999) in
           match uu____19987 with
           | (u, a, c_is) ->
               let uu____20047 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u] in
               (match uu____20047 with
                | (uu____20056, lift_t) ->
                    let lift_t_shape_error s =
                      let uu____20067 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name in
                      let uu____20069 = FStar_Ident.string_of_lid tgt in
                      let uu____20071 =
                        FStar_Syntax_Print.term_to_string lift_t in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____20067 uu____20069 s uu____20071 in
                    let uu____20074 =
                      let uu____20107 =
                        let uu____20108 = FStar_Syntax_Subst.compress lift_t in
                        uu____20108.FStar_Syntax_Syntax.n in
                      match uu____20107 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs, c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____20172 =
                            FStar_Syntax_Subst.open_comp bs c1 in
                          (match uu____20172 with
                           | (a_b::bs1, c2) ->
                               let uu____20232 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one)) in
                               (a_b, uu____20232, c2))
                      | uu____20320 ->
                          let uu____20321 =
                            let uu____20327 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders" in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____20327) in
                          FStar_Errors.raise_error uu____20321 r in
                    (match uu____20074 with
                     | (a_b, (rest_bs, f_b::[]), lift_c) ->
                         let uu____20445 =
                           let uu____20452 =
                             let uu____20453 =
                               let uu____20454 =
                                 let uu____20461 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst in
                                 (uu____20461, a) in
                               FStar_Syntax_Syntax.NT uu____20454 in
                             [uu____20453] in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____20452
                             (fun b ->
                                let uu____20478 =
                                  FStar_Syntax_Print.binder_to_string b in
                                let uu____20480 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name in
                                let uu____20482 =
                                  FStar_Ident.string_of_lid tgt in
                                let uu____20484 =
                                  FStar_Range.string_of_range r in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____20478 uu____20480 uu____20482
                                  uu____20484) r in
                         (match uu____20445 with
                          | (rest_bs_uvars, g) ->
                              ((let uu____20498 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects") in
                                if uu____20498
                                then
                                  let uu____20503 =
                                    FStar_List.fold_left
                                      (fun s ->
                                         fun u1 ->
                                           let uu____20512 =
                                             let uu____20514 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1 in
                                             Prims.op_Hat ";;;;" uu____20514 in
                                           Prims.op_Hat s uu____20512) ""
                                      rest_bs_uvars in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____20503
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b ->
                                       fun t ->
                                         let uu____20545 =
                                           let uu____20552 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst in
                                           (uu____20552, t) in
                                         FStar_Syntax_Syntax.NT uu____20545)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars) in
                                let guard_f =
                                  let f_sort =
                                    let uu____20571 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs) in
                                    FStar_All.pipe_right uu____20571
                                      FStar_Syntax_Subst.compress in
                                  let f_sort_is =
                                    let uu____20577 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name in
                                    effect_args_from_repr f_sort uu____20577
                                      r in
                                  FStar_List.fold_left2
                                    (fun g1 ->
                                       fun i1 ->
                                         fun i2 ->
                                           let uu____20586 =
                                             FStar_TypeChecker_Rel.layered_effect_teq
                                               env i1 i2
                                               (FStar_Pervasives_Native.Some
                                                  lift_name) in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____20586)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is in
                                let lift_ct =
                                  let uu____20589 =
                                    FStar_All.pipe_right lift_c
                                      (FStar_Syntax_Subst.subst_comp substs) in
                                  FStar_All.pipe_right uu____20589
                                    FStar_Syntax_Util.comp_to_comp_typ in
                                let is =
                                  let uu____20593 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____20593 r in
                                let fml =
                                  let uu____20598 =
                                    let uu____20603 =
                                      FStar_List.hd
                                        lift_ct.FStar_Syntax_Syntax.comp_univs in
                                    let uu____20604 =
                                      let uu____20605 =
                                        FStar_List.hd
                                          lift_ct.FStar_Syntax_Syntax.effect_args in
                                      FStar_Pervasives_Native.fst uu____20605 in
                                    (uu____20603, uu____20604) in
                                  match uu____20598 with
                                  | (u1, wp) ->
                                      FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                        env u1
                                        lift_ct.FStar_Syntax_Syntax.result_typ
                                        wp FStar_Range.dummyRange in
                                (let uu____20631 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects"))
                                     &&
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme) in
                                 if uu____20631
                                 then
                                   let uu____20637 =
                                     FStar_Syntax_Print.term_to_string fml in
                                   FStar_Util.print1 "Guard for lift is: %s"
                                     uu____20637
                                 else ());
                                (let c1 =
                                   let uu____20643 =
                                     let uu____20644 =
                                       FStar_All.pipe_right is
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.as_arg) in
                                     {
                                       FStar_Syntax_Syntax.comp_univs =
                                         (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                       FStar_Syntax_Syntax.effect_name = tgt;
                                       FStar_Syntax_Syntax.result_typ = a;
                                       FStar_Syntax_Syntax.effect_args =
                                         uu____20644;
                                       FStar_Syntax_Syntax.flags = []
                                     } in
                                   FStar_Syntax_Syntax.mk_Comp uu____20643 in
                                 (let uu____20668 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects") in
                                  if uu____20668
                                  then
                                    let uu____20673 =
                                      FStar_Syntax_Print.comp_to_string c1 in
                                    FStar_Util.print1 "} Lifted comp: %s\n"
                                      uu____20673
                                  else ());
                                 (let uu____20678 =
                                    let uu____20679 =
                                      FStar_TypeChecker_Env.conj_guard g
                                        guard_f in
                                    let uu____20680 =
                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                        (FStar_TypeChecker_Common.NonTrivial
                                           fml) in
                                    FStar_TypeChecker_Env.conj_guard
                                      uu____20679 uu____20680 in
                                  (c1, uu____20678)))))))))
let lift_tf_layered_effect_term :
  'uuuuuu20694 .
    'uuuuuu20694 ->
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
              let uu____20723 =
                let uu____20728 =
                  FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift
                    FStar_Util.must in
                FStar_All.pipe_right uu____20728
                  (fun ts -> FStar_TypeChecker_Env.inst_tscheme_with ts [u]) in
              FStar_All.pipe_right uu____20723 FStar_Pervasives_Native.snd in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must in
              let uu____20771 =
                let uu____20772 =
                  let uu____20775 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd in
                  FStar_All.pipe_right uu____20775
                    FStar_Syntax_Subst.compress in
                uu____20772.FStar_Syntax_Syntax.n in
              match uu____20771 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____20798::bs, uu____20800)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____20840 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one)) in
                  FStar_All.pipe_right uu____20840
                    FStar_Pervasives_Native.fst
              | uu____20946 ->
                  let uu____20947 =
                    let uu____20953 =
                      let uu____20955 =
                        FStar_Syntax_Print.tscheme_to_string lift_t in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____20955 in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____20953) in
                  FStar_Errors.raise_error uu____20947
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos in
            let args =
              let uu____20982 = FStar_Syntax_Syntax.as_arg a in
              let uu____20991 =
                let uu____21002 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____21038 ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const)) in
                let uu____21045 =
                  let uu____21056 = FStar_Syntax_Syntax.as_arg e in
                  [uu____21056] in
                FStar_List.append uu____21002 uu____21045 in
              uu____20982 :: uu____20991 in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              e.FStar_Syntax_Syntax.pos
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env ->
    fun datacon ->
      fun index ->
        let uu____21127 = FStar_TypeChecker_Env.lookup_datacon env datacon in
        match uu____21127 with
        | (uu____21132, t) ->
            let err n =
              let uu____21142 =
                let uu____21148 =
                  let uu____21150 = FStar_Ident.string_of_lid datacon in
                  let uu____21152 = FStar_Util.string_of_int n in
                  let uu____21154 = FStar_Util.string_of_int index in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____21150 uu____21152 uu____21154 in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____21148) in
              let uu____21158 = FStar_TypeChecker_Env.get_range env in
              FStar_Errors.raise_error uu____21142 uu____21158 in
            let uu____21159 =
              let uu____21160 = FStar_Syntax_Subst.compress t in
              uu____21160.FStar_Syntax_Syntax.n in
            (match uu____21159 with
             | FStar_Syntax_Syntax.Tm_arrow (bs, uu____21164) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____21219 ->
                           match uu____21219 with
                           | (uu____21227, q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true)) ->
                                    false
                                | uu____21236 -> true))) in
                 if (FStar_List.length bs1) <= index
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index in
                    FStar_Syntax_Util.mk_field_projector_name datacon
                      (FStar_Pervasives_Native.fst b) index)
             | uu____21270 -> err Prims.int_zero)
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env ->
    fun sub ->
      let uu____21283 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub.FStar_Syntax_Syntax.target) in
      if uu____21283
      then
        let uu____21286 =
          let uu____21299 =
            FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must in
          lift_tf_layered_effect sub.FStar_Syntax_Syntax.target uu____21299 in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____21286;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c in
           let uu____21334 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs in
           match uu____21334 with
           | (uu____21343, lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args in
               let uu____21362 =
                 let uu____21363 =
                   let uu___2530_21364 = ct in
                   let uu____21365 =
                     let uu____21376 =
                       let uu____21385 =
                         let uu____21386 =
                           let uu____21387 =
                             let uu____21404 =
                               let uu____21415 =
                                 FStar_Syntax_Syntax.as_arg
                                   ct.FStar_Syntax_Syntax.result_typ in
                               [uu____21415; wp] in
                             (lift_t, uu____21404) in
                           FStar_Syntax_Syntax.Tm_app uu____21387 in
                         FStar_Syntax_Syntax.mk uu____21386
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos in
                       FStar_All.pipe_right uu____21385
                         FStar_Syntax_Syntax.as_arg in
                     [uu____21376] in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2530_21364.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2530_21364.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____21365;
                     FStar_Syntax_Syntax.flags =
                       (uu___2530_21364.FStar_Syntax_Syntax.flags)
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____21363 in
               (uu____21362, FStar_TypeChecker_Common.trivial_guard) in
         let mk_mlift_term ts u r e =
           let uu____21515 = FStar_TypeChecker_Env.inst_tscheme_with ts [u] in
           match uu____21515 with
           | (uu____21522, lift_t) ->
               let uu____21524 =
                 let uu____21525 =
                   let uu____21542 =
                     let uu____21553 = FStar_Syntax_Syntax.as_arg r in
                     let uu____21562 =
                       let uu____21573 =
                         FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun in
                       let uu____21582 =
                         let uu____21593 = FStar_Syntax_Syntax.as_arg e in
                         [uu____21593] in
                       uu____21573 :: uu____21582 in
                     uu____21553 :: uu____21562 in
                   (lift_t, uu____21542) in
                 FStar_Syntax_Syntax.Tm_app uu____21525 in
               FStar_Syntax_Syntax.mk uu____21524 e.FStar_Syntax_Syntax.pos in
         let uu____21646 =
           let uu____21659 =
             FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must in
           FStar_All.pipe_right uu____21659 mk_mlift_wp in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____21646;
           FStar_TypeChecker_Env.mlift_term =
             (match sub.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____21695 ->
                        fun uu____21696 -> fun e -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env ->
    fun sub ->
      let uu____21719 = get_mlift_for_subeff env sub in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub.FStar_Syntax_Syntax.source sub.FStar_Syntax_Syntax.target
        uu____21719
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