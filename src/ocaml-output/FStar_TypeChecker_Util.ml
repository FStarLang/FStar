open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option *
    FStar_TypeChecker_Common.lcomp)
let (report : FStar_TypeChecker_Env.env -> Prims.string Prims.list -> unit) =
  fun env ->
    fun errs ->
      let uu____20 = FStar_TypeChecker_Env.get_range env in
      let uu____21 = FStar_TypeChecker_Err.failed_to_prove_specification errs in
      FStar_Errors.log_issue uu____20 uu____21
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
          let uu____78 = (FStar_Options.eager_subtyping ()) || solve_deferred in
          if uu____78
          then
            let uu____79 =
              FStar_All.pipe_right g.FStar_TypeChecker_Common.deferred
                (FStar_List.partition
                   (fun uu____125 ->
                      match uu____125 with
                      | (uu____130, p) ->
                          FStar_TypeChecker_Rel.flex_prob_closing env xs p)) in
            match uu____79 with
            | (solve_now, defer) ->
                ((let uu____159 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel") in
                  if uu____159
                  then
                    (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                     FStar_List.iter
                       (fun uu____170 ->
                          match uu____170 with
                          | (s, p) ->
                              let uu____177 =
                                FStar_TypeChecker_Rel.prob_to_string env p in
                              FStar_Util.print2 "%s: %s\n" s uu____177)
                       solve_now;
                     FStar_Util.print_string " ...DEFERRED THE REST:\n";
                     FStar_List.iter
                       (fun uu____188 ->
                          match uu____188 with
                          | (s, p) ->
                              let uu____195 =
                                FStar_TypeChecker_Rel.prob_to_string env p in
                              FStar_Util.print2 "%s: %s\n" s uu____195) defer;
                     FStar_Util.print_string "END\n")
                  else ());
                 (let g1 =
                    FStar_TypeChecker_Rel.solve_deferred_constraints env
                      (let uu___49_199 = g in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___49_199.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred_to_tac =
                           (uu___49_199.FStar_TypeChecker_Common.deferred_to_tac);
                         FStar_TypeChecker_Common.deferred = solve_now;
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___49_199.FStar_TypeChecker_Common.univ_ineqs);
                         FStar_TypeChecker_Common.implicits =
                           (uu___49_199.FStar_TypeChecker_Common.implicits)
                       }) in
                  let g2 =
                    let uu___52_201 = g1 in
                    {
                      FStar_TypeChecker_Common.guard_f =
                        (uu___52_201.FStar_TypeChecker_Common.guard_f);
                      FStar_TypeChecker_Common.deferred_to_tac =
                        (uu___52_201.FStar_TypeChecker_Common.deferred_to_tac);
                      FStar_TypeChecker_Common.deferred = defer;
                      FStar_TypeChecker_Common.univ_ineqs =
                        (uu___52_201.FStar_TypeChecker_Common.univ_ineqs);
                      FStar_TypeChecker_Common.implicits =
                        (uu___52_201.FStar_TypeChecker_Common.implicits)
                    } in
                  g2))
          else g
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r ->
    fun t ->
      let uvs = FStar_Syntax_Free.uvars t in
      let uu____216 =
        let uu____217 = FStar_Util.set_is_empty uvs in
        Prims.op_Negation uu____217 in
      if uu____216
      then
        let us =
          let uu____219 =
            let uu____222 = FStar_Util.set_elements uvs in
            FStar_List.map
              (fun u ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____222 in
          FStar_All.pipe_right uu____219 (FStar_String.concat ", ") in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____233 =
            let uu____238 =
              let uu____239 = FStar_Syntax_Print.term_to_string t in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____239 in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____238) in
          FStar_Errors.log_issue r uu____233);
         FStar_Options.pop ())
      else ()
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool))
  =
  fun env ->
    fun uu____256 ->
      match uu____256 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____266;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____268;
          FStar_Syntax_Syntax.lbpos = uu____269;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname in
          let t1 = FStar_Syntax_Subst.compress t in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown ->
               let uu____302 = FStar_Syntax_Subst.open_univ_vars univ_vars e in
               (match uu____302 with
                | (univ_vars1, e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                    let r = FStar_TypeChecker_Env.get_range env1 in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2 in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4, uu____339) -> aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4, t2, uu____346)
                          -> FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs, body, uu____401) ->
                          let res = aux body in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____437 = FStar_Options.ml_ish () in
                                if uu____437
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              c.FStar_Syntax_Syntax.pos in
                          ((let uu____456 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High in
                            if uu____456
                            then
                              let uu____457 = FStar_Range.string_of_range r in
                              let uu____458 =
                                FStar_Syntax_Print.term_to_string t2 in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____457 uu____458
                            else ());
                           FStar_Util.Inl t2)
                      | uu____460 -> FStar_Util.Inl FStar_Syntax_Syntax.tun in
                    let t2 =
                      let uu____462 = aux e1 in
                      match uu____462 with
                      | FStar_Util.Inr c ->
                          let uu____468 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c in
                          if uu____468
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____470 =
                               let uu____475 =
                                 let uu____476 =
                                   FStar_Syntax_Print.comp_to_string c in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____476 in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____475) in
                             FStar_Errors.raise_error uu____470 rng)
                      | FStar_Util.Inl t2 -> t2 in
                    (univ_vars1, t2, true))
           | uu____480 ->
               let uu____481 = FStar_Syntax_Subst.open_univ_vars univ_vars t1 in
               (match uu____481 with
                | (univ_vars1, t2) -> (univ_vars1, t2, false)))
let rec (decorated_pattern_as_term :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun pat ->
    let mk f = FStar_Syntax_Syntax.mk f pat.FStar_Syntax_Syntax.p in
    let pat_as_arg uu____540 =
      match uu____540 with
      | (p, i) ->
          let uu____557 = decorated_pattern_as_term p in
          (match uu____557 with
           | (vars, te) ->
               let uu____580 =
                 let uu____585 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____585) in
               (vars, uu____580)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____599 = mk (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____599)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____603 = mk (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____603)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____607 = mk (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____607)
    | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
        let uu____628 =
          let uu____647 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____647 FStar_List.unzip in
        (match uu____628 with
         | (vars, args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____783 =
               let uu____784 =
                 let uu____785 =
                   let uu____802 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____802, args) in
                 FStar_Syntax_Syntax.Tm_app uu____785 in
               mk uu____784 in
             (vars1, uu____783))
    | FStar_Syntax_Syntax.Pat_dot_term (x, e) -> ([], e)
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____840, uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____850, uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd::uu____864 -> FStar_Pervasives_Native.Some hd)
let (lcomp_univ_opt :
  FStar_TypeChecker_Common.lcomp ->
    (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option *
      FStar_TypeChecker_Common.guard_t))
  =
  fun lc ->
    let uu____878 =
      FStar_All.pipe_right lc FStar_TypeChecker_Common.lcomp_comp in
    FStar_All.pipe_right uu____878
      (fun uu____906 ->
         match uu____906 with | (c, g) -> ((comp_univ_opt c), g))
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
            let uu____977 =
              let uu____978 =
                let uu____989 = FStar_Syntax_Syntax.as_arg wp in [uu____989] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____978;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____977
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
        let err uu____1069 =
          let uu____1070 =
            let uu____1075 =
              let uu____1076 = FStar_Syntax_Print.term_to_string repr in
              let uu____1077 = FStar_Util.string_of_bool is_layered in
              FStar_Util.format2
                "Could not get effect args from repr %s with is_layered %s"
                uu____1076 uu____1077 in
            (FStar_Errors.Fatal_UnexpectedEffect, uu____1075) in
          FStar_Errors.raise_error uu____1070 r in
        let repr1 = FStar_Syntax_Subst.compress repr in
        if is_layered
        then
          match repr1.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_app (uu____1085, uu____1086::is) ->
              FStar_All.pipe_right is
                (FStar_List.map FStar_Pervasives_Native.fst)
          | uu____1154 -> err ()
        else
          (match repr1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (uu____1158, c) ->
               let uu____1180 =
                 FStar_All.pipe_right c FStar_Syntax_Util.comp_to_comp_typ in
               FStar_All.pipe_right uu____1180
                 (fun ct ->
                    FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                      (FStar_List.map FStar_Pervasives_Native.fst))
           | uu____1215 -> err ())
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
                let uu____1247 =
                  let uu____1248 =
                    FStar_TypeChecker_Env.lid_exists env
                      FStar_Parser_Const.effect_GTot_lid in
                  FStar_All.pipe_left Prims.op_Negation uu____1248 in
                if uu____1247
                then FStar_Syntax_Syntax.mk_Total a
                else
                  (let uu____1250 = FStar_Syntax_Util.is_unit a in
                   if uu____1250
                   then
                     FStar_Syntax_Syntax.mk_Total' a
                       (FStar_Pervasives_Native.Some
                          FStar_Syntax_Syntax.U_zero)
                   else
                     (let wp =
                        let uu____1253 =
                          env.FStar_TypeChecker_Env.lax &&
                            (FStar_Options.ml_ish ()) in
                        if uu____1253
                        then FStar_Syntax_Syntax.tun
                        else
                          (let ret_wp =
                             FStar_All.pipe_right ed
                               FStar_Syntax_Util.get_return_vc_combinator in
                           let uu____1256 =
                             let uu____1257 =
                               FStar_TypeChecker_Env.inst_effect_fun_with
                                 [u_a] env ed ret_wp in
                             let uu____1258 =
                               let uu____1259 = FStar_Syntax_Syntax.as_arg a in
                               let uu____1268 =
                                 let uu____1279 =
                                   FStar_Syntax_Syntax.as_arg e in
                                 [uu____1279] in
                               uu____1259 :: uu____1268 in
                             FStar_Syntax_Syntax.mk_Tm_app uu____1257
                               uu____1258 e.FStar_Syntax_Syntax.pos in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____1256) in
                      mk_comp ed u_a a wp [FStar_Syntax_Syntax.RETURN])) in
              (let uu____1313 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Return") in
               if uu____1313
               then
                 let uu____1314 =
                   FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                 let uu____1315 = FStar_Syntax_Print.term_to_string e in
                 let uu____1316 =
                   FStar_TypeChecker_Normalize.comp_to_string env c in
                 FStar_Util.print3 "(%s) returning %s at comp type %s\n"
                   uu____1314 uu____1315 uu____1316
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
              (let uu____1357 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "LayeredEffects") in
               if uu____1357
               then
                 let uu____1358 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                 let uu____1359 = FStar_Syntax_Print.univ_to_string u_a in
                 let uu____1360 = FStar_Syntax_Print.term_to_string a in
                 let uu____1361 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print4
                   "Computing %s.return for u_a:%s, a:%s, and e:%s{\n"
                   uu____1358 uu____1359 uu____1360 uu____1361
               else ());
              (let uu____1363 =
                 let uu____1368 =
                   FStar_All.pipe_right ed
                     FStar_Syntax_Util.get_return_vc_combinator in
                 FStar_TypeChecker_Env.inst_tscheme_with uu____1368 [u_a] in
               match uu____1363 with
               | (uu____1373, return_t) ->
                   let return_t_shape_error s =
                     let uu____1385 =
                       let uu____1386 =
                         FStar_Ident.string_of_lid
                           ed.FStar_Syntax_Syntax.mname in
                       let uu____1387 =
                         FStar_Syntax_Print.term_to_string return_t in
                       FStar_Util.format3
                         "%s.return %s does not have proper shape (reason:%s)"
                         uu____1386 uu____1387 s in
                     (FStar_Errors.Fatal_UnexpectedEffect, uu____1385) in
                   let uu____1388 =
                     let uu____1417 =
                       let uu____1418 = FStar_Syntax_Subst.compress return_t in
                       uu____1418.FStar_Syntax_Syntax.n in
                     match uu____1417 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                         (FStar_List.length bs) >= (Prims.of_int (2)) ->
                         let uu____1477 = FStar_Syntax_Subst.open_comp bs c in
                         (match uu____1477 with
                          | (a_b::x_b::bs1, c1) ->
                              let uu____1546 =
                                FStar_Syntax_Util.comp_to_comp_typ c1 in
                              (a_b, x_b, bs1, uu____1546))
                     | uu____1567 ->
                         let uu____1568 =
                           return_t_shape_error
                             "Either not an arrow or not enough binders" in
                         FStar_Errors.raise_error uu____1568 r in
                   (match uu____1388 with
                    | (a_b, x_b, rest_bs, return_ct) ->
                        let uu____1649 =
                          let uu____1656 =
                            let uu____1657 =
                              let uu____1658 =
                                let uu____1665 =
                                  FStar_All.pipe_right a_b
                                    FStar_Pervasives_Native.fst in
                                (uu____1665, a) in
                              FStar_Syntax_Syntax.NT uu____1658 in
                            let uu____1676 =
                              let uu____1679 =
                                let uu____1680 =
                                  let uu____1687 =
                                    FStar_All.pipe_right x_b
                                      FStar_Pervasives_Native.fst in
                                  (uu____1687, e) in
                                FStar_Syntax_Syntax.NT uu____1680 in
                              [uu____1679] in
                            uu____1657 :: uu____1676 in
                          FStar_TypeChecker_Env.uvars_for_binders env rest_bs
                            uu____1656
                            (fun b ->
                               let uu____1703 =
                                 FStar_Syntax_Print.binder_to_string b in
                               let uu____1704 =
                                 let uu____1705 =
                                   FStar_Ident.string_of_lid
                                     ed.FStar_Syntax_Syntax.mname in
                                 FStar_Util.format1 "%s.return" uu____1705 in
                               let uu____1706 = FStar_Range.string_of_range r in
                               FStar_Util.format3
                                 "implicit var for binder %s of %s at %s"
                                 uu____1703 uu____1704 uu____1706) r in
                        (match uu____1649 with
                         | (rest_bs_uvars, g_uvars) ->
                             let subst =
                               FStar_List.map2
                                 (fun b ->
                                    fun t ->
                                      let uu____1741 =
                                        let uu____1748 =
                                          FStar_All.pipe_right b
                                            FStar_Pervasives_Native.fst in
                                        (uu____1748, t) in
                                      FStar_Syntax_Syntax.NT uu____1741) (a_b
                                 :: x_b :: rest_bs) (a :: e :: rest_bs_uvars) in
                             let is =
                               let uu____1774 =
                                 let uu____1777 =
                                   FStar_Syntax_Subst.compress
                                     return_ct.FStar_Syntax_Syntax.result_typ in
                                 let uu____1778 =
                                   FStar_Syntax_Util.is_layered ed in
                                 effect_args_from_repr uu____1777 uu____1778
                                   r in
                               FStar_All.pipe_right uu____1774
                                 (FStar_List.map
                                    (FStar_Syntax_Subst.subst subst)) in
                             let c =
                               let uu____1784 =
                                 let uu____1785 =
                                   FStar_All.pipe_right is
                                     (FStar_List.map
                                        FStar_Syntax_Syntax.as_arg) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs = [u_a];
                                   FStar_Syntax_Syntax.effect_name =
                                     (ed.FStar_Syntax_Syntax.mname);
                                   FStar_Syntax_Syntax.result_typ = a;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____1785;
                                   FStar_Syntax_Syntax.flags = []
                                 } in
                               FStar_Syntax_Syntax.mk_Comp uu____1784 in
                             ((let uu____1809 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffects") in
                               if uu____1809
                               then
                                 let uu____1810 =
                                   FStar_Syntax_Print.comp_to_string c in
                                 FStar_Util.print1 "} c after return %s\n"
                                   uu____1810
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
              let uu____1850 =
                FStar_All.pipe_right ed FStar_Syntax_Util.is_layered in
              if uu____1850
              then mk_indexed_return env ed u_a a e r
              else
                (let uu____1856 = mk_wp_return env ed u_a a e r in
                 (uu____1856, FStar_TypeChecker_Env.trivial_guard))
let (lift_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp_typ ->
      FStar_TypeChecker_Env.mlift ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun c ->
      fun lift ->
        let uu____1880 =
          FStar_All.pipe_right
            (let uu___257_1882 = c in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___257_1882.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___257_1882.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ =
                 (uu___257_1882.FStar_Syntax_Syntax.result_typ);
               FStar_Syntax_Syntax.effect_args =
                 (uu___257_1882.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags = []
             }) FStar_Syntax_Syntax.mk_Comp in
        FStar_All.pipe_right uu____1880
          (lift.FStar_TypeChecker_Env.mlift_wp env)
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env ->
    fun l1_in ->
      fun l2_in ->
        let uu____1902 =
          let uu____1907 = FStar_TypeChecker_Env.norm_eff_name env l1_in in
          let uu____1908 = FStar_TypeChecker_Env.norm_eff_name env l2_in in
          (uu____1907, uu____1908) in
        match uu____1902 with
        | (l1, l2) ->
            let uu____1911 = FStar_TypeChecker_Env.join_opt env l1 l2 in
            (match uu____1911 with
             | FStar_Pervasives_Native.Some (m, uu____1921, uu____1922) -> m
             | FStar_Pervasives_Native.None ->
                 let uu____1935 =
                   FStar_TypeChecker_Env.exists_polymonadic_bind env l1 l2 in
                 (match uu____1935 with
                  | FStar_Pervasives_Native.Some (m, uu____1949) -> m
                  | FStar_Pervasives_Native.None ->
                      let uu____1982 =
                        let uu____1987 =
                          let uu____1988 =
                            FStar_Syntax_Print.lid_to_string l1_in in
                          let uu____1989 =
                            FStar_Syntax_Print.lid_to_string l2_in in
                          FStar_Util.format2
                            "Effects %s and %s cannot be composed" uu____1988
                            uu____1989 in
                        (FStar_Errors.Fatal_EffectsCannotBeComposed,
                          uu____1987) in
                      FStar_Errors.raise_error uu____1982
                        env.FStar_TypeChecker_Env.range))
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env ->
    fun c1 ->
      fun c2 ->
        let uu____2005 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2) in
        if uu____2005
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
            let uu____2058 =
              FStar_TypeChecker_Env.join_opt env
                c11.FStar_Syntax_Syntax.effect_name
                c21.FStar_Syntax_Syntax.effect_name in
            match uu____2058 with
            | FStar_Pervasives_Native.Some (m, lift1, lift2) ->
                let uu____2086 = lift_comp env c11 lift1 in
                (match uu____2086 with
                 | (c12, g1) ->
                     let uu____2103 =
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
                          let uu____2140 = lift_comp env_x c21 lift2 in
                          match uu____2140 with
                          | (c22, g2) ->
                              let uu____2151 =
                                FStar_TypeChecker_Env.close_guard env 
                                  [x_a] g2 in
                              (c22, uu____2151)) in
                     (match uu____2103 with
                      | (c22, g2) -> (m, c12, c22, g1, g2)))
            | FStar_Pervasives_Native.None ->
                let uu____2182 =
                  let uu____2187 =
                    let uu____2188 =
                      FStar_Syntax_Print.lid_to_string
                        c11.FStar_Syntax_Syntax.effect_name in
                    let uu____2189 =
                      FStar_Syntax_Print.lid_to_string
                        c21.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2 "Effects %s and %s cannot be composed"
                      uu____2188 uu____2189 in
                  (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____2187) in
                FStar_Errors.raise_error uu____2182
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
            let uu____2245 = lift_comps_sep_guards env c1 c2 b for_bind in
            match uu____2245 with
            | (l, c11, c21, g1, g2) ->
                let uu____2269 = FStar_TypeChecker_Env.conj_guard g1 g2 in
                (l, c11, c21, uu____2269)
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
          let uu____2331 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid in
          if uu____2331
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____2338 =
      let uu____2339 = FStar_Syntax_Subst.compress t in
      uu____2339.FStar_Syntax_Syntax.n in
    match uu____2338 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2342 -> true
    | uu____2357 -> false
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
              let uu____2414 =
                let uu____2415 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____2415 in
              if uu____2414
              then f
              else (let uu____2417 = reason1 () in label uu____2417 r f)
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
            let uu___354_2434 = g in
            let uu____2435 =
              let uu____2436 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____2436 in
            {
              FStar_TypeChecker_Common.guard_f = uu____2435;
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___354_2434.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___354_2434.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___354_2434.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___354_2434.FStar_TypeChecker_Common.implicits)
            }
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun bvs ->
      fun c ->
        let uu____2456 = FStar_Syntax_Util.is_ml_comp c in
        if uu____2456
        then c
        else
          (let uu____2458 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____2458
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close =
                  let uu____2497 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator in
                  FStar_All.pipe_right uu____2497 FStar_Util.must in
                FStar_List.fold_right
                  (fun x ->
                     fun wp ->
                       let bs =
                         let uu____2526 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____2526] in
                       let us =
                         let uu____2548 =
                           let uu____2551 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____2551] in
                         u_res :: uu____2548 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu____2557 =
                         FStar_TypeChecker_Env.inst_effect_fun_with us env md
                           close in
                       let uu____2558 =
                         let uu____2559 = FStar_Syntax_Syntax.as_arg res_t in
                         let uu____2568 =
                           let uu____2579 =
                             FStar_Syntax_Syntax.as_arg
                               x.FStar_Syntax_Syntax.sort in
                           let uu____2588 =
                             let uu____2599 = FStar_Syntax_Syntax.as_arg wp1 in
                             [uu____2599] in
                           uu____2579 :: uu____2588 in
                         uu____2559 :: uu____2568 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____2557 uu____2558
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____2641 = destruct_wp_comp c1 in
              match uu____2641 with
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
                let uu____2680 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs) in
                FStar_All.pipe_right uu____2680
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
                  let uu____2728 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs) in
                  FStar_All.pipe_right uu____2728
                    (close_guard_implicits env false bs)))
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_2737 ->
            match uu___0_2737 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> true
            | uu____2738 -> false))
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env ->
    fun eopt ->
      fun lc ->
        let lc_is_unit_or_effectful =
          let uu____2759 =
            let uu____2762 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp in
            FStar_All.pipe_right uu____2762 FStar_Pervasives_Native.snd in
          FStar_All.pipe_right uu____2759
            (fun c ->
               (let uu____2785 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c in
                Prims.op_Negation uu____2785) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____2787 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c in
                     Prims.op_Negation uu____2787))) in
        match eopt with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____2795 = FStar_Syntax_Util.head_and_args' e in
                match uu____2795 with
                | (head, uu____2811) ->
                    let uu____2832 =
                      let uu____2833 = FStar_Syntax_Util.un_uinst head in
                      uu____2833.FStar_Syntax_Syntax.n in
                    (match uu____2832 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2837 =
                           let uu____2838 = FStar_Syntax_Syntax.lid_of_fv fv in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____2838 in
                         Prims.op_Negation uu____2837
                     | uu____2839 -> true)))
              &&
              (let uu____2841 = should_not_inline_lc lc in
               Prims.op_Negation uu____2841)
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
            let uu____2885 =
              FStar_TypeChecker_Env.get_effect_decl env eff_lid in
            mk_return env uu____2885 u t v v.FStar_Syntax_Syntax.pos
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
                        let uu____2953 =
                          let uu____2954 =
                            FStar_All.pipe_right m FStar_Ident.ident_of_lid in
                          FStar_All.pipe_right uu____2954
                            FStar_Ident.string_of_id in
                        let uu____2955 =
                          let uu____2956 =
                            FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                          FStar_All.pipe_right uu____2956
                            FStar_Ident.string_of_id in
                        let uu____2957 =
                          let uu____2958 =
                            FStar_All.pipe_right p FStar_Ident.ident_of_lid in
                          FStar_All.pipe_right uu____2958
                            FStar_Ident.string_of_id in
                        FStar_Util.format3 "(%s, %s) |> %s" uu____2953
                          uu____2955 uu____2957 in
                      (let uu____2960 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LayeredEffects") in
                       if uu____2960
                       then
                         let uu____2961 =
                           let uu____2962 = FStar_Syntax_Syntax.mk_Comp ct1 in
                           FStar_Syntax_Print.comp_to_string uu____2962 in
                         let uu____2963 =
                           let uu____2964 = FStar_Syntax_Syntax.mk_Comp ct2 in
                           FStar_Syntax_Print.comp_to_string uu____2964 in
                         FStar_Util.print2 "Binding c1:%s and c2:%s {\n"
                           uu____2961 uu____2963
                       else ());
                      (let uu____2967 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "ResolveImplicitsHook") in
                       if uu____2967
                       then
                         let uu____2968 =
                           let uu____2969 =
                             FStar_TypeChecker_Env.get_range env in
                           FStar_Range.string_of_range uu____2969 in
                         let uu____2970 =
                           FStar_Syntax_Print.tscheme_to_string bind_t in
                         FStar_Util.print2
                           "///////////////////////////////Bind at %s/////////////////////\nwith bind_t = %s\n"
                           uu____2968 uu____2970
                       else ());
                      (let uu____2972 =
                         let uu____2979 =
                           FStar_TypeChecker_Env.get_effect_decl env m in
                         let uu____2980 =
                           FStar_TypeChecker_Env.get_effect_decl env n in
                         let uu____2981 =
                           FStar_TypeChecker_Env.get_effect_decl env p in
                         (uu____2979, uu____2980, uu____2981) in
                       match uu____2972 with
                       | (m_ed, n_ed, p_ed) ->
                           let uu____2989 =
                             let uu____3002 =
                               FStar_List.hd
                                 ct1.FStar_Syntax_Syntax.comp_univs in
                             let uu____3003 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 ct1.FStar_Syntax_Syntax.effect_args in
                             (uu____3002,
                               (ct1.FStar_Syntax_Syntax.result_typ),
                               uu____3003) in
                           (match uu____2989 with
                            | (u1, t1, is1) ->
                                let uu____3047 =
                                  let uu____3060 =
                                    FStar_List.hd
                                      ct2.FStar_Syntax_Syntax.comp_univs in
                                  let uu____3061 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst
                                      ct2.FStar_Syntax_Syntax.effect_args in
                                  (uu____3060,
                                    (ct2.FStar_Syntax_Syntax.result_typ),
                                    uu____3061) in
                                (match uu____3047 with
                                 | (u2, t2, is2) ->
                                     let uu____3105 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         bind_t [u1; u2] in
                                     (match uu____3105 with
                                      | (uu____3114, bind_t1) ->
                                          let bind_t_shape_error s =
                                            let uu____3126 =
                                              let uu____3127 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t1 in
                                              FStar_Util.format3
                                                "bind %s (%s) does not have proper shape (reason:%s)"
                                                uu____3127 bind_name s in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu____3126) in
                                          let uu____3128 =
                                            let uu____3173 =
                                              let uu____3174 =
                                                FStar_Syntax_Subst.compress
                                                  bind_t1 in
                                              uu____3174.FStar_Syntax_Syntax.n in
                                            match uu____3173 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs, c) when
                                                (FStar_List.length bs) >=
                                                  (Prims.of_int (4))
                                                ->
                                                let uu____3249 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs c in
                                                (match uu____3249 with
                                                 | (a_b::b_b::bs1, c1) ->
                                                     let uu____3334 =
                                                       let uu____3361 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2)))
                                                           bs1 in
                                                       FStar_All.pipe_right
                                                         uu____3361
                                                         (fun uu____3445 ->
                                                            match uu____3445
                                                            with
                                                            | (l1, l2) ->
                                                                let uu____3526
                                                                  =
                                                                  FStar_List.hd
                                                                    l2 in
                                                                let uu____3539
                                                                  =
                                                                  let uu____3546
                                                                    =
                                                                    FStar_List.tl
                                                                    l2 in
                                                                  FStar_List.hd
                                                                    uu____3546 in
                                                                (l1,
                                                                  uu____3526,
                                                                  uu____3539)) in
                                                     (match uu____3334 with
                                                      | (rest_bs, f_b, g_b)
                                                          ->
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b, c1)))
                                            | uu____3706 ->
                                                let uu____3707 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders" in
                                                FStar_Errors.raise_error
                                                  uu____3707 r1 in
                                          (match uu____3128 with
                                           | (a_b, b_b, rest_bs, f_b, g_b,
                                              bind_c) ->
                                               let uu____3830 =
                                                 let uu____3837 =
                                                   let uu____3838 =
                                                     let uu____3839 =
                                                       let uu____3846 =
                                                         FStar_All.pipe_right
                                                           a_b
                                                           FStar_Pervasives_Native.fst in
                                                       (uu____3846, t1) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____3839 in
                                                   let uu____3857 =
                                                     let uu____3860 =
                                                       let uu____3861 =
                                                         let uu____3868 =
                                                           FStar_All.pipe_right
                                                             b_b
                                                             FStar_Pervasives_Native.fst in
                                                         (uu____3868, t2) in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____3861 in
                                                     [uu____3860] in
                                                   uu____3838 :: uu____3857 in
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs uu____3837
                                                   (fun b1 ->
                                                      let uu____3883 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1 in
                                                      let uu____3884 =
                                                        FStar_Range.string_of_range
                                                          r1 in
                                                      FStar_Util.format3
                                                        "implicit var for binder %s of %s at %s"
                                                        uu____3883 bind_name
                                                        uu____3884) r1 in
                                               (match uu____3830 with
                                                | (rest_bs_uvars, g_uvars) ->
                                                    ((let uu____3896 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "ResolveImplicitsHook") in
                                                      if uu____3896
                                                      then
                                                        FStar_All.pipe_right
                                                          rest_bs_uvars
                                                          (FStar_List.iter
                                                             (fun t ->
                                                                let uu____3906
                                                                  =
                                                                  let uu____3907
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    t in
                                                                  uu____3907.FStar_Syntax_Syntax.n in
                                                                match uu____3906
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (u,
                                                                    uu____3911)
                                                                    ->
                                                                    let uu____3928
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t in
                                                                    let uu____3929
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
                                                                    uu____3933
                                                                    ->
                                                                    "<no attr>" in
                                                                    FStar_Util.print2
                                                                    "Generated uvar %s with attribute %s\n"
                                                                    uu____3928
                                                                    uu____3929))
                                                      else ());
                                                     (let subst =
                                                        FStar_List.map2
                                                          (fun b1 ->
                                                             fun t ->
                                                               let uu____3961
                                                                 =
                                                                 let uu____3968
                                                                   =
                                                                   FStar_All.pipe_right
                                                                    b1
                                                                    FStar_Pervasives_Native.fst in
                                                                 (uu____3968,
                                                                   t) in
                                                               FStar_Syntax_Syntax.NT
                                                                 uu____3961)
                                                          (a_b :: b_b ::
                                                          rest_bs) (t1 :: t2
                                                          :: rest_bs_uvars) in
                                                      let f_guard =
                                                        let f_sort_is =
                                                          let uu____3997 =
                                                            let uu____4000 =
                                                              let uu____4001
                                                                =
                                                                let uu____4002
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    f_b
                                                                    FStar_Pervasives_Native.fst in
                                                                uu____4002.FStar_Syntax_Syntax.sort in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4001 in
                                                            let uu____4011 =
                                                              FStar_Syntax_Util.is_layered
                                                                m_ed in
                                                            effect_args_from_repr
                                                              uu____4000
                                                              uu____4011 r1 in
                                                          FStar_All.pipe_right
                                                            uu____3997
                                                            (FStar_List.map
                                                               (FStar_Syntax_Subst.subst
                                                                  subst)) in
                                                        FStar_List.fold_left2
                                                          (fun g ->
                                                             fun i1 ->
                                                               fun f_i1 ->
                                                                 (let uu____4035
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "ResolveImplicitsHook") in
                                                                  if
                                                                    uu____4035
                                                                  then
                                                                    let uu____4036
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    i1 in
                                                                    let uu____4037
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    f_i1 in
                                                                    FStar_Util.print2
                                                                    "Generating constraint %s = %s\n"
                                                                    uu____4036
                                                                    uu____4037
                                                                  else ());
                                                                 (let uu____4039
                                                                    =
                                                                    FStar_TypeChecker_Rel.layered_effect_teq
                                                                    env i1
                                                                    f_i1
                                                                    (FStar_Pervasives_Native.Some
                                                                    bind_name) in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____4039))
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
                                                          let uu____4058 =
                                                            let uu____4059 =
                                                              let uu____4062
                                                                =
                                                                let uu____4063
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    g_b
                                                                    FStar_Pervasives_Native.fst in
                                                                uu____4063.FStar_Syntax_Syntax.sort in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4062 in
                                                            uu____4059.FStar_Syntax_Syntax.n in
                                                          match uu____4058
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_arrow
                                                              (bs, c) ->
                                                              let uu____4096
                                                                =
                                                                FStar_Syntax_Subst.open_comp
                                                                  bs c in
                                                              (match uu____4096
                                                               with
                                                               | (bs1, c1) ->
                                                                   let bs_subst
                                                                    =
                                                                    let uu____4106
                                                                    =
                                                                    let uu____4113
                                                                    =
                                                                    let uu____4114
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1 in
                                                                    FStar_All.pipe_right
                                                                    uu____4114
                                                                    FStar_Pervasives_Native.fst in
                                                                    let uu____4135
                                                                    =
                                                                    let uu____4138
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst in
                                                                    FStar_All.pipe_right
                                                                    uu____4138
                                                                    FStar_Syntax_Syntax.bv_to_name in
                                                                    (uu____4113,
                                                                    uu____4135) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4106 in
                                                                   let c2 =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1 in
                                                                   let uu____4152
                                                                    =
                                                                    let uu____4155
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2) in
                                                                    let uu____4156
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed in
                                                                    effect_args_from_repr
                                                                    uu____4155
                                                                    uu____4156
                                                                    r1 in
                                                                   FStar_All.pipe_right
                                                                    uu____4152
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst)))
                                                          | uu____4161 ->
                                                              failwith
                                                                "impossible: mk_indexed_bind" in
                                                        let env_g =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env [x_a] in
                                                        let uu____4177 =
                                                          FStar_List.fold_left2
                                                            (fun g ->
                                                               fun i1 ->
                                                                 fun g_i1 ->
                                                                   (let uu____4195
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "ResolveImplicitsHook") in
                                                                    if
                                                                    uu____4195
                                                                    then
                                                                    let uu____4196
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    i1 in
                                                                    let uu____4197
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    g_i1 in
                                                                    FStar_Util.print2
                                                                    "Generating constraint %s = %s\n"
                                                                    uu____4196
                                                                    uu____4197
                                                                    else ());
                                                                   (let uu____4199
                                                                    =
                                                                    FStar_TypeChecker_Rel.layered_effect_teq
                                                                    env_g i1
                                                                    g_i1
                                                                    (FStar_Pervasives_Native.Some
                                                                    bind_name) in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____4199))
                                                            FStar_TypeChecker_Env.trivial_guard
                                                            is2 g_sort_is in
                                                        FStar_All.pipe_right
                                                          uu____4177
                                                          (FStar_TypeChecker_Env.close_guard
                                                             env [x_a]) in
                                                      let bind_ct =
                                                        let uu____4213 =
                                                          FStar_All.pipe_right
                                                            bind_c
                                                            (FStar_Syntax_Subst.subst_comp
                                                               subst) in
                                                        FStar_All.pipe_right
                                                          uu____4213
                                                          FStar_Syntax_Util.comp_to_comp_typ in
                                                      let fml =
                                                        let uu____4215 =
                                                          let uu____4220 =
                                                            FStar_List.hd
                                                              bind_ct.FStar_Syntax_Syntax.comp_univs in
                                                          let uu____4221 =
                                                            let uu____4222 =
                                                              FStar_List.hd
                                                                bind_ct.FStar_Syntax_Syntax.effect_args in
                                                            FStar_Pervasives_Native.fst
                                                              uu____4222 in
                                                          (uu____4220,
                                                            uu____4221) in
                                                        match uu____4215 with
                                                        | (u, wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              bind_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange in
                                                      let is =
                                                        let uu____4248 =
                                                          FStar_Syntax_Subst.compress
                                                            bind_ct.FStar_Syntax_Syntax.result_typ in
                                                        let uu____4249 =
                                                          FStar_Syntax_Util.is_layered
                                                            p_ed in
                                                        effect_args_from_repr
                                                          uu____4248
                                                          uu____4249 r1 in
                                                      let c =
                                                        let uu____4251 =
                                                          let uu____4252 =
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
                                                              = uu____4252;
                                                            FStar_Syntax_Syntax.flags
                                                              = flags
                                                          } in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____4251 in
                                                      (let uu____4272 =
                                                         FStar_All.pipe_left
                                                           (FStar_TypeChecker_Env.debug
                                                              env)
                                                           (FStar_Options.Other
                                                              "LayeredEffects") in
                                                       if uu____4272
                                                       then
                                                         let uu____4273 =
                                                           FStar_Syntax_Print.comp_to_string
                                                             c in
                                                         FStar_Util.print1
                                                           "} c after bind: %s\n"
                                                           uu____4273
                                                       else ());
                                                      (let guard =
                                                         let uu____4276 =
                                                           let uu____4279 =
                                                             let uu____4282 =
                                                               let uu____4285
                                                                 =
                                                                 let uu____4288
                                                                   =
                                                                   FStar_TypeChecker_Env.guard_of_guard_formula
                                                                    (FStar_TypeChecker_Common.NonTrivial
                                                                    fml) in
                                                                 [uu____4288] in
                                                               g_guard ::
                                                                 uu____4285 in
                                                             f_guard ::
                                                               uu____4282 in
                                                           g_uvars ::
                                                             uu____4279 in
                                                         FStar_TypeChecker_Env.conj_guards
                                                           uu____4276 in
                                                       (let uu____4290 =
                                                          FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "ResolveImplicitsHook") in
                                                        if uu____4290
                                                        then
                                                          let uu____4291 =
                                                            let uu____4292 =
                                                              FStar_TypeChecker_Env.get_range
                                                                env in
                                                            FStar_Range.string_of_range
                                                              uu____4292 in
                                                          let uu____4293 =
                                                            FStar_TypeChecker_Rel.guard_to_string
                                                              env guard in
                                                          FStar_Util.print2
                                                            "///////////////////////////////EndBind at %s/////////////////////\nguard = %s\n"
                                                            uu____4291
                                                            uu____4293
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
                let uu____4338 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m in
                  let uu____4364 = FStar_TypeChecker_Env.wp_signature env m in
                  match uu____4364 with
                  | (a, kwp) ->
                      let uu____4395 = destruct_wp_comp ct1 in
                      let uu____4402 = destruct_wp_comp ct2 in
                      ((md, a, kwp), uu____4395, uu____4402) in
                match uu____4338 with
                | ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None ->
                          let uu____4455 = FStar_Syntax_Syntax.null_binder t1 in
                          [uu____4455]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____4475 = FStar_Syntax_Syntax.mk_binder x in
                          [uu____4475] in
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
                      let uu____4522 = FStar_Syntax_Syntax.as_arg r11 in
                      let uu____4531 =
                        let uu____4542 = FStar_Syntax_Syntax.as_arg t1 in
                        let uu____4551 =
                          let uu____4562 = FStar_Syntax_Syntax.as_arg t2 in
                          let uu____4571 =
                            let uu____4582 = FStar_Syntax_Syntax.as_arg wp1 in
                            let uu____4591 =
                              let uu____4602 =
                                let uu____4611 = mk_lam wp2 in
                                FStar_Syntax_Syntax.as_arg uu____4611 in
                              [uu____4602] in
                            uu____4582 :: uu____4591 in
                          uu____4562 :: uu____4571 in
                        uu____4542 :: uu____4551 in
                      uu____4522 :: uu____4531 in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator in
                    let wp =
                      let uu____4662 =
                        FStar_TypeChecker_Env.inst_effect_fun_with
                          [u_t1; u_t2] env md bind_wp in
                      FStar_Syntax_Syntax.mk_Tm_app uu____4662 wp_args
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
              let uu____4709 =
                let uu____4714 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1 in
                let uu____4715 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2 in
                (uu____4714, uu____4715) in
              match uu____4709 with
              | (ct1, ct2) ->
                  let uu____4722 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name in
                  (match uu____4722 with
                   | FStar_Pervasives_Native.Some (p, f_bind) ->
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None ->
                       let uu____4773 = lift_comps env c1 c2 b true in
                       (match uu____4773 with
                        | (m, c11, c21, g_lift) ->
                            let uu____4790 =
                              let uu____4795 =
                                FStar_Syntax_Util.comp_to_comp_typ c11 in
                              let uu____4796 =
                                FStar_Syntax_Util.comp_to_comp_typ c21 in
                              (uu____4795, uu____4796) in
                            (match uu____4790 with
                             | (ct11, ct21) ->
                                 let uu____4803 =
                                   let uu____4808 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m in
                                   if uu____4808
                                   then
                                     let bind_t =
                                       let uu____4814 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env) in
                                       FStar_All.pipe_right uu____4814
                                         FStar_Syntax_Util.get_bind_vc_combinator in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu____4816 =
                                        mk_wp_bind env m ct11 b ct21 flags r1 in
                                      (uu____4816,
                                        FStar_TypeChecker_Env.trivial_guard)) in
                                 (match uu____4803 with
                                  | (c, g_bind) ->
                                      let uu____4823 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind in
                                      (c, uu____4823)))))
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
            let uu____4858 =
              let uu____4859 =
                let uu____4870 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg in
                [uu____4870] in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____4859;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____4858 in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags ->
    let uu____4914 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_4918 ->
              match uu___1_4918 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> true
              | uu____4919 -> false)) in
    if uu____4914
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_4928 ->
              match uu___2_4928 with
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
        let uu____4955 = FStar_Syntax_Util.is_ml_comp c in
        if uu____4955
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
           let pure_assume_wp =
             let uu____4963 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None in
             FStar_Syntax_Syntax.fv_to_tm uu____4963 in
           let pure_assume_wp1 =
             let uu____4965 =
               let uu____4966 =
                 FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula in
               [uu____4966] in
             let uu____4999 = FStar_TypeChecker_Env.get_range env in
             FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____4965
               uu____4999 in
           let uu____5000 = weaken_flags ct.FStar_Syntax_Syntax.flags in
           bind_pure_wp_with env pure_assume_wp1 c uu____5000)
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env ->
    fun lc ->
      fun f ->
        let weaken uu____5027 =
          let uu____5028 = FStar_TypeChecker_Common.lcomp_comp lc in
          match uu____5028 with
          | (c, g_c) ->
              let uu____5039 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
              if uu____5039
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5050 = weaken_comp env c f1 in
                     (match uu____5050 with
                      | (c1, g_w) ->
                          let uu____5061 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w in
                          (c1, uu____5061))) in
        let uu____5062 = weaken_flags lc.FStar_TypeChecker_Common.cflags in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5062 weaken
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
                 let uu____5114 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None in
                 FStar_Syntax_Syntax.fv_to_tm uu____5114 in
               let pure_assert_wp1 =
                 let uu____5116 =
                   let uu____5117 =
                     let uu____5126 = label_opt env reason r f in
                     FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                       uu____5126 in
                   [uu____5117] in
                 FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____5116 r in
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
            let uu____5193 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0 in
            if uu____5193
            then (lc, g0)
            else
              (let flags =
                 let uu____5202 =
                   let uu____5209 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc in
                   if uu____5209
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, []) in
                 match uu____5202 with
                 | (maybe_trivial_post, flags) ->
                     let uu____5229 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_5237 ->
                               match uu___3_5237 with
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
                               | uu____5240 -> [])) in
                     FStar_List.append flags uu____5229 in
               let strengthen uu____5250 =
                 let uu____5251 = FStar_TypeChecker_Common.lcomp_comp lc in
                 match uu____5251 with
                 | (c, g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                        let uu____5268 = FStar_TypeChecker_Env.guard_form g01 in
                        match uu____5268 with
                        | FStar_TypeChecker_Common.Trivial -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____5275 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____5275
                              then
                                let uu____5276 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only in
                                let uu____5277 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____5276 uu____5277
                              else ());
                             (let uu____5279 =
                                strengthen_comp env reason c f flags in
                              match uu____5279 with
                              | (c1, g_s) ->
                                  let uu____5290 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s in
                                  (c1, uu____5290)))) in
               let uu____5291 =
                 let uu____5292 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name in
                 FStar_TypeChecker_Common.mk_lcomp uu____5292
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen in
               (uu____5291,
                 (let uu___678_5294 = g0 in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred_to_tac =
                      (uu___678_5294.FStar_TypeChecker_Common.deferred_to_tac);
                    FStar_TypeChecker_Common.deferred =
                      (uu___678_5294.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___678_5294.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___678_5294.FStar_TypeChecker_Common.implicits)
                  })))
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_5301 ->
            match uu___4_5301 with
            | FStar_Syntax_Syntax.SOMETRIVIAL -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION -> true
            | uu____5302 -> false) lc.FStar_TypeChecker_Common.cflags)
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
          let uu____5329 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax in
          if uu____5329
          then e
          else
            (let uu____5333 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____5335 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid in
                  FStar_Option.isSome uu____5335) in
             if uu____5333
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
                | uu____5400 -> false in
              if is_unit
              then
                let uu____5405 =
                  let uu____5406 =
                    let uu____5407 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name in
                    FStar_All.pipe_right uu____5407
                      (FStar_TypeChecker_Env.norm_eff_name env) in
                  FStar_All.pipe_right uu____5406
                    (FStar_TypeChecker_Env.is_layered_effect env) in
                (if uu____5405
                 then
                   let uu____5414 = FStar_Syntax_Subst.open_term_bv b phi in
                   match uu____5414 with
                   | (b1, phi1) ->
                       let phi2 =
                         FStar_Syntax_Subst.subst
                           [FStar_Syntax_Syntax.NT
                              (b1, FStar_Syntax_Syntax.unit_const)] phi1 in
                       weaken_comp env c phi2
                 else
                   (let uu____5429 = close_wp_comp env [x] c in
                    (uu____5429, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____5431 -> (c, FStar_TypeChecker_Env.trivial_guard)
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
          fun uu____5458 ->
            match uu____5458 with
            | (b, lc2) ->
                let debug f =
                  let uu____5478 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____5478 then f () else () in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                let bind_flags =
                  let uu____5486 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21) in
                  if uu____5486
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____5493 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11 in
                       if uu____5493
                       then
                         let uu____5496 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21 in
                         (if uu____5496
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5500 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21 in
                             if uu____5500
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5505 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21) in
                          if uu____5505
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else []) in
                     let uu____5509 = lcomp_has_trivial_postcondition lc21 in
                     if uu____5509
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags) in
                let bind_it uu____5522 =
                  let uu____5523 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ()) in
                  if uu____5523
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ in
                    let uu____5529 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ [] in
                    (uu____5529, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____5531 =
                       FStar_TypeChecker_Common.lcomp_comp lc11 in
                     match uu____5531 with
                     | (c1, g_c1) ->
                         let uu____5542 =
                           FStar_TypeChecker_Common.lcomp_comp lc21 in
                         (match uu____5542 with
                          | (c2, g_c2) ->
                              let trivial_guard =
                                let uu____5554 =
                                  match b with
                                  | FStar_Pervasives_Native.Some x ->
                                      let b1 =
                                        FStar_Syntax_Syntax.mk_binder x in
                                      let uu____5557 =
                                        FStar_Syntax_Syntax.is_null_binder b1 in
                                      if uu____5557
                                      then g_c2
                                      else
                                        FStar_TypeChecker_Env.close_guard env
                                          [b1] g_c2
                                  | FStar_Pervasives_Native.None -> g_c2 in
                                FStar_TypeChecker_Env.conj_guard g_c1
                                  uu____5554 in
                              (debug
                                 (fun uu____5580 ->
                                    let uu____5581 =
                                      FStar_Syntax_Print.comp_to_string c1 in
                                    let uu____5582 =
                                      match b with
                                      | FStar_Pervasives_Native.None ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x in
                                    let uu____5584 =
                                      FStar_Syntax_Print.comp_to_string c2 in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____5581 uu____5582 uu____5584);
                               (let aux uu____5598 =
                                  let uu____5599 =
                                    FStar_Syntax_Util.is_trivial_wp c1 in
                                  if uu____5599
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____5620
                                        ->
                                        let uu____5621 =
                                          FStar_Syntax_Util.is_ml_comp c2 in
                                        (if uu____5621
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____5640 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2) in
                                     if uu____5640
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML") in
                                let try_simplify uu____5673 =
                                  let aux_with_trivial_guard uu____5699 =
                                    let uu____5700 = aux () in
                                    match uu____5700 with
                                    | FStar_Util.Inl (c, reason) ->
                                        FStar_Util.Inl
                                          (c, trivial_guard, reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason in
                                  let uu____5742 =
                                    let uu____5743 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid in
                                    FStar_Option.isNone uu____5743 in
                                  if uu____5742
                                  then
                                    let uu____5756 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2) in
                                    (if uu____5756
                                     then
                                       FStar_Util.Inl
                                         (c2, trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____5774 =
                                          FStar_TypeChecker_Env.get_range env in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____5774))
                                  else
                                    (let uu____5786 =
                                       FStar_Syntax_Util.is_total_comp c1 in
                                     if uu____5786
                                     then
                                       let close_with_type_of_x x c =
                                         let x1 =
                                           let uu___781_5813 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___781_5813.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___781_5813.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         maybe_capture_unit_refinement env
                                           x1.FStar_Syntax_Syntax.sort x1 c in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some e,
                                          FStar_Pervasives_Native.Some x) ->
                                           let uu____5842 =
                                             let uu____5847 =
                                               FStar_All.pipe_right c2
                                                 (FStar_Syntax_Subst.subst_comp
                                                    [FStar_Syntax_Syntax.NT
                                                       (x, e)]) in
                                             FStar_All.pipe_right uu____5847
                                               (close_with_type_of_x x) in
                                           (match uu____5842 with
                                            | (c21, g_close) ->
                                                let uu____5866 =
                                                  let uu____5873 =
                                                    let uu____5874 =
                                                      let uu____5877 =
                                                        let uu____5880 =
                                                          FStar_TypeChecker_Env.map_guard
                                                            g_c2
                                                            (FStar_Syntax_Subst.subst
                                                               [FStar_Syntax_Syntax.NT
                                                                  (x, e)]) in
                                                        [uu____5880; g_close] in
                                                      g_c1 :: uu____5877 in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____5874 in
                                                  (c21, uu____5873, "c1 Tot") in
                                                FStar_Util.Inl uu____5866)
                                       | (uu____5889,
                                          FStar_Pervasives_Native.Some x) ->
                                           let uu____5901 =
                                             FStar_All.pipe_right c2
                                               (close_with_type_of_x x) in
                                           (match uu____5901 with
                                            | (c21, g_close) ->
                                                let uu____5922 =
                                                  let uu____5929 =
                                                    let uu____5930 =
                                                      let uu____5933 =
                                                        let uu____5936 =
                                                          let uu____5937 =
                                                            let uu____5938 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x in
                                                            [uu____5938] in
                                                          FStar_TypeChecker_Env.close_guard
                                                            env uu____5937
                                                            g_c2 in
                                                        [uu____5936; g_close] in
                                                      g_c1 :: uu____5933 in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____5930 in
                                                  (c21, uu____5929,
                                                    "c1 Tot only close") in
                                                FStar_Util.Inl uu____5922)
                                       | (uu____5963, uu____5964) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____5978 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2) in
                                        if uu____5978
                                        then
                                          let uu____5989 =
                                            let uu____5996 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2) in
                                            (uu____5996, trivial_guard,
                                              "both GTot") in
                                          FStar_Util.Inl uu____5989
                                        else aux_with_trivial_guard ())) in
                                let uu____6004 = try_simplify () in
                                match uu____6004 with
                                | FStar_Util.Inl (c, g, reason) ->
                                    (debug
                                       (fun uu____6033 ->
                                          let uu____6034 =
                                            FStar_Syntax_Print.comp_to_string
                                              c in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____6034);
                                     (c, g))
                                | FStar_Util.Inr reason ->
                                    (debug
                                       (fun uu____6045 ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 g =
                                        let uu____6075 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1 in
                                        match uu____6075 with
                                        | (c, g_bind) ->
                                            let uu____6086 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g g_bind in
                                            (c, uu____6086) in
                                      let mk_seq c11 b1 c21 =
                                        let c12 =
                                          FStar_TypeChecker_Env.unfold_effect_abbrev
                                            env c11 in
                                        let c22 =
                                          FStar_TypeChecker_Env.unfold_effect_abbrev
                                            env c21 in
                                        let uu____6113 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name in
                                        match uu____6113 with
                                        | (m, uu____6125, lift2) ->
                                            let uu____6127 =
                                              lift_comp env c22 lift2 in
                                            (match uu____6127 with
                                             | (c23, g2) ->
                                                 let uu____6138 =
                                                   destruct_wp_comp c12 in
                                                 (match uu____6138 with
                                                  | (u1, t1, wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name in
                                                      let trivial =
                                                        let uu____6154 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator in
                                                        FStar_All.pipe_right
                                                          uu____6154
                                                          FStar_Util.must in
                                                      let vc1 =
                                                        let uu____6162 =
                                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                                            [u1] env
                                                            md_pure_or_ghost
                                                            trivial in
                                                        let uu____6163 =
                                                          let uu____6164 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              t1 in
                                                          let uu____6173 =
                                                            let uu____6184 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                wp1 in
                                                            [uu____6184] in
                                                          uu____6164 ::
                                                            uu____6173 in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____6162
                                                          uu____6163 r1 in
                                                      let uu____6217 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags in
                                                      (match uu____6217 with
                                                       | (c, g_s) ->
                                                           let uu____6231 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s] in
                                                           (c, uu____6231)))) in
                                      let uu____6232 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1 in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None ->
                                            let uu____6248 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t in
                                            (uu____6248, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t) in
                                      match uu____6232 with
                                      | (u_res_t1, res_t1) ->
                                          let uu____6264 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11) in
                                          if uu____6264
                                          then
                                            let e1 = FStar_Option.get e1opt in
                                            let x = FStar_Option.get b in
                                            let uu____6271 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1 in
                                            (if uu____6271
                                             then
                                               (debug
                                                  (fun uu____6283 ->
                                                     let uu____6284 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1 in
                                                     let uu____6285 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____6284 uu____6285);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2 in
                                                 let g =
                                                   let uu____6290 =
                                                     FStar_TypeChecker_Env.map_guard
                                                       g_c2
                                                       (FStar_Syntax_Subst.subst
                                                          [FStar_Syntax_Syntax.NT
                                                             (x, e1)]) in
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 uu____6290 in
                                                 mk_bind1 c1 b c21 g))
                                             else
                                               (let uu____6294 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____6296 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid in
                                                     FStar_Option.isSome
                                                       uu____6296) in
                                                if uu____6294
                                                then
                                                  let e1' =
                                                    let uu____6320 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        () in
                                                    if uu____6320
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1 in
                                                  (debug
                                                     (fun uu____6329 ->
                                                        let uu____6330 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1' in
                                                        let uu____6331 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____6330
                                                          uu____6331);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2 in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug
                                                     (fun uu____6343 ->
                                                        let uu____6344 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1 in
                                                        let uu____6345 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____6344
                                                          uu____6345);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2 in
                                                    let x_eq_e =
                                                      let uu____6350 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____6350 in
                                                    let uu____6351 =
                                                      let uu____6356 =
                                                        let uu____6357 =
                                                          let uu____6358 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x in
                                                          [uu____6358] in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____6357 in
                                                      weaken_comp uu____6356
                                                        c21 x_eq_e in
                                                    match uu____6351 with
                                                    | (c22, g_w) ->
                                                        let g =
                                                          let uu____6384 =
                                                            let uu____6385 =
                                                              let uu____6386
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x in
                                                              [uu____6386] in
                                                            let uu____6405 =
                                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                                g_c2 x_eq_e in
                                                            FStar_TypeChecker_Env.close_guard
                                                              env uu____6385
                                                              uu____6405 in
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g_c1 uu____6384 in
                                                        let uu____6406 =
                                                          mk_bind1 c1 b c22 g in
                                                        (match uu____6406
                                                         with
                                                         | (c, g_bind) ->
                                                             let uu____6417 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind in
                                                             (c, uu____6417))))))
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
      | uu____6432 -> g2
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
            let uu____6462 =
              (FStar_All.pipe_right m_opt FStar_Util.is_none) ||
                (is_ghost_effect env lc.FStar_TypeChecker_Common.eff_name) in
            if uu____6462
            then FStar_Parser_Const.effect_PURE_lid
            else FStar_All.pipe_right m_opt FStar_Util.must in
          let flags =
            let uu____6471 = FStar_TypeChecker_Common.is_total_lcomp lc in
            if uu____6471
            then FStar_Syntax_Syntax.RETURN ::
              (lc.FStar_TypeChecker_Common.cflags)
            else FStar_Syntax_Syntax.PARTIAL_RETURN ::
              (lc.FStar_TypeChecker_Common.cflags) in
          let refine uu____6484 =
            let uu____6489 = FStar_TypeChecker_Common.lcomp_comp lc in
            match uu____6489 with
            | (c, g_c) ->
                let u_t =
                  match comp_univ_opt c with
                  | FStar_Pervasives_Native.Some u_t -> u_t
                  | FStar_Pervasives_Native.None ->
                      env.FStar_TypeChecker_Env.universe_of env
                        (FStar_Syntax_Util.comp_result c) in
                let uu____6502 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____6502
                then
                  let uu____6507 =
                    return_value env m (FStar_Pervasives_Native.Some u_t)
                      (FStar_Syntax_Util.comp_result c) e in
                  (match uu____6507 with
                   | (retc, g_retc) ->
                       let g_c1 = FStar_TypeChecker_Env.conj_guard g_c g_retc in
                       let uu____6519 =
                         let uu____6520 = FStar_Syntax_Util.is_pure_comp c in
                         Prims.op_Negation uu____6520 in
                       if uu____6519
                       then
                         let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                         let retc2 =
                           let uu___910_6527 = retc1 in
                           {
                             FStar_Syntax_Syntax.comp_univs =
                               (uu___910_6527.FStar_Syntax_Syntax.comp_univs);
                             FStar_Syntax_Syntax.effect_name =
                               FStar_Parser_Const.effect_GHOST_lid;
                             FStar_Syntax_Syntax.result_typ =
                               (uu___910_6527.FStar_Syntax_Syntax.result_typ);
                             FStar_Syntax_Syntax.effect_args =
                               (uu___910_6527.FStar_Syntax_Syntax.effect_args);
                             FStar_Syntax_Syntax.flags = flags
                           } in
                         let uu____6528 = FStar_Syntax_Syntax.mk_Comp retc2 in
                         (uu____6528, g_c1)
                       else
                         (let uu____6530 =
                            FStar_Syntax_Util.comp_set_flags retc flags in
                          (uu____6530, g_c1)))
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
                   let uu____6540 =
                     return_value env_x m (FStar_Pervasives_Native.Some u_t)
                       t xexp in
                   match uu____6540 with
                   | (ret, g_ret) ->
                       let ret1 =
                         let uu____6552 =
                           FStar_Syntax_Util.comp_set_flags ret
                             [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                         FStar_All.pipe_left
                           FStar_TypeChecker_Common.lcomp_of_comp uu____6552 in
                       let eq = FStar_Syntax_Util.mk_eq2 u_t t xexp e in
                       let eq_ret =
                         weaken_precondition env_x ret1
                           (FStar_TypeChecker_Common.NonTrivial eq) in
                       let uu____6555 =
                         let uu____6560 =
                           let uu____6561 =
                             FStar_TypeChecker_Common.lcomp_of_comp c2 in
                           bind e.FStar_Syntax_Syntax.pos env
                             FStar_Pervasives_Native.None uu____6561
                             ((FStar_Pervasives_Native.Some x), eq_ret) in
                         FStar_TypeChecker_Common.lcomp_comp uu____6560 in
                       (match uu____6555 with
                        | (bind_c, g_bind) ->
                            let uu____6570 =
                              FStar_Syntax_Util.comp_set_flags bind_c flags in
                            let uu____6571 =
                              FStar_TypeChecker_Env.conj_guards
                                [g_c; g_ret; g_bind] in
                            (uu____6570, uu____6571))) in
          let uu____6572 = should_not_inline_lc lc in
          if uu____6572
          then
            let uu____6573 =
              let uu____6578 =
                let uu____6579 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format1
                  "assume_result_eq_pure_term cannot inline an non-inlineable lc : %s"
                  uu____6579 in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____6578) in
            FStar_Errors.raise_error uu____6573 e.FStar_Syntax_Syntax.pos
          else
            (let uu____6581 = refine () in
             match uu____6581 with
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
              (let uu____6614 =
                 FStar_TypeChecker_Common.is_lcomp_partial_return lc in
               Prims.op_Negation uu____6614) in
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
            fun uu____6662 ->
              match uu____6662 with
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
                    let uu____6676 =
                      ((FStar_Ident.lid_equals eff2
                          FStar_Parser_Const.effect_PURE_lid)
                         &&
                         (let uu____6678 =
                            FStar_TypeChecker_Env.join_opt env eff1 eff2 in
                          FStar_All.pipe_right uu____6678 FStar_Util.is_none))
                        &&
                        (let uu____6702 =
                           FStar_TypeChecker_Env.exists_polymonadic_bind env
                             eff1 eff2 in
                         FStar_All.pipe_right uu____6702 FStar_Util.is_none) in
                    if uu____6676
                    then
                      let uu____6737 =
                        FStar_All.pipe_right eff1
                          (fun uu____6742 ->
                             FStar_Pervasives_Native.Some uu____6742) in
                      assume_result_eq_pure_term_in_m env_x uu____6737 e2 lc2
                    else
                      (let uu____6744 =
                         ((let uu____6747 = is_pure_or_ghost_effect env eff1 in
                           Prims.op_Negation uu____6747) ||
                            (should_not_inline_lc lc1))
                           && (is_pure_or_ghost_effect env eff2) in
                       if uu____6744
                       then
                         let uu____6748 =
                           FStar_All.pipe_right eff1
                             (fun uu____6753 ->
                                FStar_Pervasives_Native.Some uu____6753) in
                         maybe_assume_result_eq_pure_term_in_m env_x
                           uu____6748 e2 lc2
                       else lc2) in
                  bind r env e1opt lc1 (x, lc21)
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun lid ->
      let uu____6767 =
        let uu____6768 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____6768 in
      FStar_Syntax_Syntax.fvar uu____6767 FStar_Syntax_Syntax.delta_constant
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
                    let uu____6818 =
                      FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                    FStar_Util.format1 "%s.conjunction" uu____6818 in
                  let uu____6819 =
                    let uu____6824 =
                      let uu____6825 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator in
                      FStar_All.pipe_right uu____6825 FStar_Util.must in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____6824 [u_a] in
                  match uu____6819 with
                  | (uu____6836, conjunction) ->
                      let uu____6838 =
                        let uu____6847 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args in
                        let uu____6862 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args in
                        (uu____6847, uu____6862) in
                      (match uu____6838 with
                       | (is1, is2) ->
                           let conjunction_t_error s =
                             let uu____6905 =
                               let uu____6906 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction in
                               FStar_Util.format3
                                 "conjunction %s (%s) does not have proper shape (reason:%s)"
                                 uu____6906 conjunction_name s in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____6905) in
                           let uu____6907 =
                             let uu____6952 =
                               let uu____6953 =
                                 FStar_Syntax_Subst.compress conjunction in
                               uu____6953.FStar_Syntax_Syntax.n in
                             match uu____6952 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs, body, uu____7002) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____7033 =
                                   FStar_Syntax_Subst.open_term bs body in
                                 (match uu____7033 with
                                  | (a_b::bs1, body1) ->
                                      let uu____7105 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1 in
                                      (match uu____7105 with
                                       | (rest_bs, f_b::g_b::p_b::[]) ->
                                           let uu____7252 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____7252)))
                             | uu____7285 ->
                                 let uu____7286 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders" in
                                 FStar_Errors.raise_error uu____7286 r in
                           (match uu____6907 with
                            | (a_b, rest_bs, f_b, g_b, p_b, body) ->
                                let uu____7409 =
                                  let uu____7416 =
                                    let uu____7417 =
                                      let uu____7418 =
                                        let uu____7425 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst in
                                        (uu____7425, a) in
                                      FStar_Syntax_Syntax.NT uu____7418 in
                                    [uu____7417] in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____7416
                                    (fun b ->
                                       let uu____7441 =
                                         FStar_Syntax_Print.binder_to_string
                                           b in
                                       let uu____7442 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname in
                                       let uu____7443 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____7441 uu____7442 uu____7443) r in
                                (match uu____7409 with
                                 | (rest_bs_uvars, g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b ->
                                            fun t ->
                                              let uu____7478 =
                                                let uu____7485 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst in
                                                (uu____7485, t) in
                                              FStar_Syntax_Syntax.NT
                                                uu____7478) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p])) in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____7524 =
                                           let uu____7525 =
                                             let uu____7528 =
                                               let uu____7529 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst in
                                               uu____7529.FStar_Syntax_Syntax.sort in
                                             FStar_Syntax_Subst.compress
                                               uu____7528 in
                                           uu____7525.FStar_Syntax_Syntax.n in
                                         match uu____7524 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____7540, uu____7541::is) ->
                                             let uu____7583 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst) in
                                             FStar_All.pipe_right uu____7583
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____7616 ->
                                             let uu____7617 =
                                               conjunction_t_error
                                                 "f's type is not a repr type" in
                                             FStar_Errors.raise_error
                                               uu____7617 r in
                                       FStar_List.fold_left2
                                         (fun g ->
                                            fun i1 ->
                                              fun f_i ->
                                                let uu____7631 =
                                                  FStar_TypeChecker_Rel.layered_effect_teq
                                                    env i1 f_i
                                                    (FStar_Pervasives_Native.Some
                                                       conjunction_name) in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____7631)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____7636 =
                                           let uu____7637 =
                                             let uu____7640 =
                                               let uu____7641 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst in
                                               uu____7641.FStar_Syntax_Syntax.sort in
                                             FStar_Syntax_Subst.compress
                                               uu____7640 in
                                           uu____7637.FStar_Syntax_Syntax.n in
                                         match uu____7636 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____7652, uu____7653::is) ->
                                             let uu____7695 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst) in
                                             FStar_All.pipe_right uu____7695
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____7728 ->
                                             let uu____7729 =
                                               conjunction_t_error
                                                 "g's type is not a repr type" in
                                             FStar_Errors.raise_error
                                               uu____7729 r in
                                       FStar_List.fold_left2
                                         (fun g ->
                                            fun i2 ->
                                              fun g_i ->
                                                let uu____7743 =
                                                  FStar_TypeChecker_Rel.layered_effect_teq
                                                    env i2 g_i
                                                    (FStar_Pervasives_Native.Some
                                                       conjunction_name) in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____7743)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body in
                                     let is =
                                       let uu____7748 =
                                         let uu____7749 =
                                           FStar_Syntax_Subst.compress body1 in
                                         uu____7749.FStar_Syntax_Syntax.n in
                                       match uu____7748 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____7754, a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____7809 ->
                                           let uu____7810 =
                                             conjunction_t_error
                                               "body is not a repr type" in
                                           FStar_Errors.raise_error
                                             uu____7810 r in
                                     let uu____7817 =
                                       let uu____7818 =
                                         let uu____7819 =
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
                                             uu____7819;
                                           FStar_Syntax_Syntax.flags = []
                                         } in
                                       FStar_Syntax_Syntax.mk_Comp uu____7818 in
                                     let uu____7842 =
                                       let uu____7843 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____7843 g_guard in
                                     (uu____7817, uu____7842))))
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
                fun uu____7887 ->
                  let if_then_else =
                    let uu____7893 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator in
                    FStar_All.pipe_right uu____7893 FStar_Util.must in
                  let uu____7900 = destruct_wp_comp ct1 in
                  match uu____7900 with
                  | (uu____7911, uu____7912, wp_t) ->
                      let uu____7914 = destruct_wp_comp ct2 in
                      (match uu____7914 with
                       | (uu____7925, uu____7926, wp_e) ->
                           let wp =
                             let uu____7929 =
                               FStar_TypeChecker_Env.inst_effect_fun_with
                                 [u_a] env ed if_then_else in
                             let uu____7930 =
                               let uu____7931 = FStar_Syntax_Syntax.as_arg a in
                               let uu____7940 =
                                 let uu____7951 =
                                   FStar_Syntax_Syntax.as_arg p in
                                 let uu____7960 =
                                   let uu____7971 =
                                     FStar_Syntax_Syntax.as_arg wp_t in
                                   let uu____7980 =
                                     let uu____7991 =
                                       FStar_Syntax_Syntax.as_arg wp_e in
                                     [uu____7991] in
                                   uu____7971 :: uu____7980 in
                                 uu____7951 :: uu____7960 in
                               uu____7931 :: uu____7940 in
                             let uu____8040 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Syntax.mk_Tm_app uu____7929
                               uu____7930 uu____8040 in
                           let uu____8041 = mk_comp ed u_a a wp [] in
                           (uu____8041, FStar_TypeChecker_Env.trivial_guard))
let (comp_pure_wp_false :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun u ->
      fun t ->
        let post_k =
          let uu____8060 =
            let uu____8069 = FStar_Syntax_Syntax.null_binder t in
            [uu____8069] in
          let uu____8088 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
          FStar_Syntax_Util.arrow uu____8060 uu____8088 in
        let kwp =
          let uu____8094 =
            let uu____8103 = FStar_Syntax_Syntax.null_binder post_k in
            [uu____8103] in
          let uu____8122 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
          FStar_Syntax_Util.arrow uu____8094 uu____8122 in
        let post =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k in
        let wp =
          let uu____8129 =
            let uu____8130 = FStar_Syntax_Syntax.mk_binder post in
            [uu____8130] in
          let uu____8149 = fvar_const env FStar_Parser_Const.false_lid in
          FStar_Syntax_Util.abs uu____8129 uu____8149
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
            let uu____8205 =
              let uu____8206 =
                FStar_All.pipe_right scrutinee FStar_Syntax_Syntax.mk_binder in
              [uu____8206] in
            FStar_TypeChecker_Env.push_binders env0 uu____8205 in
          let eff =
            FStar_List.fold_left
              (fun eff ->
                 fun uu____8252 ->
                   match uu____8252 with
                   | (uu____8265, eff_label, uu____8267, uu____8268) ->
                       join_effects env eff eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases in
          let uu____8279 =
            let uu____8286 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu____8320 ->
                      match uu____8320 with
                      | (uu____8333, uu____8334, flags, uu____8336) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___5_8350 ->
                                  match uu___5_8350 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE ->
                                      true
                                  | uu____8351 -> false)))) in
            if uu____8286
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, []) in
          match uu____8279 with
          | (should_not_inline_whole_match, bind_cases_flags) ->
              let bind_cases uu____8378 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
                let uu____8380 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
                if uu____8380
                then
                  let uu____8385 = lax_mk_tot_or_comp_l eff u_res_t res_t [] in
                  (uu____8385, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let maybe_return eff_label_then cthen =
                     let uu____8403 =
                       should_not_inline_whole_match ||
                         (let uu____8405 = is_pure_or_ghost_effect env eff in
                          Prims.op_Negation uu____8405) in
                     if uu____8403 then cthen true else cthen false in
                   let uu____8407 =
                     let uu____8418 =
                       let uu____8431 =
                         let uu____8436 =
                           let uu____8447 =
                             FStar_All.pipe_right lcases
                               (FStar_List.map
                                  (fun uu____8495 ->
                                     match uu____8495 with
                                     | (g, uu____8513, uu____8514,
                                        uu____8515) -> g)) in
                           FStar_All.pipe_right uu____8447
                             (FStar_List.fold_left
                                (fun uu____8561 ->
                                   fun g ->
                                     match uu____8561 with
                                     | (conds, acc) ->
                                         let cond =
                                           let uu____8602 =
                                             FStar_Syntax_Util.mk_neg g in
                                           FStar_Syntax_Util.mk_conj acc
                                             uu____8602 in
                                         ((FStar_List.append conds [cond]),
                                           cond))
                                ([FStar_Syntax_Util.t_true],
                                  FStar_Syntax_Util.t_true)) in
                         FStar_All.pipe_right uu____8436
                           FStar_Pervasives_Native.fst in
                       FStar_All.pipe_right uu____8431
                         (fun l ->
                            FStar_List.splitAt
                              ((FStar_List.length l) - Prims.int_one) l) in
                     FStar_All.pipe_right uu____8418
                       (fun uu____8699 ->
                          match uu____8699 with
                          | (l1, l2) ->
                              let uu____8740 = FStar_List.hd l2 in
                              (l1, uu____8740)) in
                   match uu____8407 with
                   | (neg_branch_conds, exhaustiveness_branch_cond) ->
                       let uu____8769 =
                         match lcases with
                         | [] ->
                             let uu____8799 =
                               comp_pure_wp_false env u_res_t res_t in
                             (FStar_Pervasives_Native.None, uu____8799,
                               FStar_TypeChecker_Env.trivial_guard)
                         | uu____8802 ->
                             let uu____8818 =
                               let uu____8850 =
                                 let uu____8861 =
                                   FStar_All.pipe_right neg_branch_conds
                                     (FStar_List.splitAt
                                        ((FStar_List.length lcases) -
                                           Prims.int_one)) in
                                 FStar_All.pipe_right uu____8861
                                   (fun uu____8931 ->
                                      match uu____8931 with
                                      | (l1, l2) ->
                                          let uu____8972 = FStar_List.hd l2 in
                                          (l1, uu____8972)) in
                               match uu____8850 with
                               | (neg_branch_conds1, neg_last) ->
                                   let uu____9028 =
                                     let uu____9065 =
                                       FStar_All.pipe_right lcases
                                         (FStar_List.splitAt
                                            ((FStar_List.length lcases) -
                                               Prims.int_one)) in
                                     FStar_All.pipe_right uu____9065
                                       (fun uu____9265 ->
                                          match uu____9265 with
                                          | (l1, l2) ->
                                              let uu____9408 =
                                                FStar_List.hd l2 in
                                              (l1, uu____9408)) in
                                   (match uu____9028 with
                                    | (lcases1,
                                       (g_last, eff_last, uu____9505, c_last))
                                        ->
                                        let uu____9570 =
                                          let lc =
                                            maybe_return eff_last c_last in
                                          let uu____9576 =
                                            FStar_TypeChecker_Common.lcomp_comp
                                              lc in
                                          match uu____9576 with
                                          | (c, g) ->
                                              let uu____9587 =
                                                let uu____9588 =
                                                  FStar_Syntax_Util.mk_conj
                                                    g_last neg_last in
                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                  g uu____9588 in
                                              (c, uu____9587) in
                                        (match uu____9570 with
                                         | (c, g) ->
                                             let uu____9622 =
                                               let uu____9623 =
                                                 FStar_All.pipe_right
                                                   eff_last
                                                   (FStar_TypeChecker_Env.norm_eff_name
                                                      env) in
                                               FStar_All.pipe_right
                                                 uu____9623
                                                 (FStar_TypeChecker_Env.get_effect_decl
                                                    env) in
                                             (lcases1, neg_branch_conds1,
                                               uu____9622, c, g))) in
                             (match uu____8818 with
                              | (lcases1, neg_branch_conds1, md, comp,
                                 g_comp) ->
                                  FStar_List.fold_right2
                                    (fun uu____9751 ->
                                       fun neg_cond ->
                                         fun uu____9753 ->
                                           match (uu____9751, uu____9753)
                                           with
                                           | ((g, eff_label, uu____9811,
                                               cthen),
                                              (uu____9813, celse, g_comp1))
                                               ->
                                               let uu____9857 =
                                                 let uu____9862 =
                                                   maybe_return eff_label
                                                     cthen in
                                                 FStar_TypeChecker_Common.lcomp_comp
                                                   uu____9862 in
                                               (match uu____9857 with
                                                | (cthen1, g_then) ->
                                                    let uu____9873 =
                                                      let uu____9884 =
                                                        lift_comps_sep_guards
                                                          env cthen1 celse
                                                          FStar_Pervasives_Native.None
                                                          false in
                                                      match uu____9884 with
                                                      | (m, cthen2, celse1,
                                                         g_lift_then,
                                                         g_lift_else) ->
                                                          let md1 =
                                                            FStar_TypeChecker_Env.get_effect_decl
                                                              env m in
                                                          let uu____9911 =
                                                            FStar_All.pipe_right
                                                              cthen2
                                                              FStar_Syntax_Util.comp_to_comp_typ in
                                                          let uu____9912 =
                                                            FStar_All.pipe_right
                                                              celse1
                                                              FStar_Syntax_Util.comp_to_comp_typ in
                                                          (md1, uu____9911,
                                                            uu____9912,
                                                            g_lift_then,
                                                            g_lift_else) in
                                                    (match uu____9873 with
                                                     | (md1, ct_then,
                                                        ct_else, g_lift_then,
                                                        g_lift_else) ->
                                                         let fn =
                                                           let uu____9963 =
                                                             FStar_All.pipe_right
                                                               md1
                                                               FStar_Syntax_Util.is_layered in
                                                           if uu____9963
                                                           then
                                                             mk_layered_conjunction
                                                           else
                                                             mk_non_layered_conjunction in
                                                         let uu____9993 =
                                                           let uu____9998 =
                                                             FStar_TypeChecker_Env.get_range
                                                               env in
                                                           fn env md1 u_res_t
                                                             res_t g ct_then
                                                             ct_else
                                                             uu____9998 in
                                                         (match uu____9993
                                                          with
                                                          | (c,
                                                             g_conjunction)
                                                              ->
                                                              let g_then1 =
                                                                let uu____10010
                                                                  =
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_then
                                                                    g_lift_then in
                                                                let uu____10011
                                                                  =
                                                                  FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    g in
                                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                                  uu____10010
                                                                  uu____10011 in
                                                              let g_else =
                                                                let uu____10013
                                                                  =
                                                                  let uu____10014
                                                                    =
                                                                    FStar_Syntax_Util.mk_neg
                                                                    g in
                                                                  FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    uu____10014 in
                                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                                  g_lift_else
                                                                  uu____10013 in
                                                              let uu____10017
                                                                =
                                                                FStar_TypeChecker_Env.conj_guards
                                                                  [g_comp1;
                                                                  g_then1;
                                                                  g_else;
                                                                  g_conjunction] in
                                                              ((FStar_Pervasives_Native.Some
                                                                  md1), c,
                                                                uu____10017)))))
                                    lcases1 neg_branch_conds1
                                    ((FStar_Pervasives_Native.Some md), comp,
                                      g_comp)) in
                       (match uu____8769 with
                        | (md, comp, g_comp) ->
                            let uu____10033 =
                              let uu____10038 =
                                let check =
                                  FStar_Syntax_Util.mk_imp
                                    exhaustiveness_branch_cond
                                    FStar_Syntax_Util.t_false in
                                let check1 =
                                  let uu____10045 =
                                    FStar_TypeChecker_Env.get_range env in
                                  label
                                    FStar_TypeChecker_Err.exhaustiveness_check
                                    uu____10045 check in
                                strengthen_comp env
                                  FStar_Pervasives_Native.None comp check1
                                  bind_cases_flags in
                              match uu____10038 with
                              | (c, g) ->
                                  let uu____10055 =
                                    FStar_TypeChecker_Env.conj_guard g_comp g in
                                  (c, uu____10055) in
                            (match uu____10033 with
                             | (comp1, g_comp1) ->
                                 let g_comp2 =
                                   let uu____10063 =
                                     let uu____10064 =
                                       FStar_All.pipe_right scrutinee
                                         FStar_Syntax_Syntax.mk_binder in
                                     [uu____10064] in
                                   FStar_TypeChecker_Env.close_guard env0
                                     uu____10063 g_comp1 in
                                 (match lcases with
                                  | [] -> (comp1, g_comp2)
                                  | uu____10106::[] -> (comp1, g_comp2)
                                  | uu____10146 ->
                                      let uu____10162 =
                                        let uu____10163 =
                                          FStar_All.pipe_right md
                                            FStar_Util.must in
                                        FStar_All.pipe_right uu____10163
                                          FStar_Syntax_Util.is_layered in
                                      if uu____10162
                                      then (comp1, g_comp2)
                                      else
                                        (let comp2 =
                                           FStar_TypeChecker_Env.comp_to_comp_typ
                                             env comp1 in
                                         let md1 =
                                           FStar_TypeChecker_Env.get_effect_decl
                                             env
                                             comp2.FStar_Syntax_Syntax.effect_name in
                                         let uu____10173 =
                                           destruct_wp_comp comp2 in
                                         match uu____10173 with
                                         | (uu____10184, uu____10185, wp) ->
                                             let ite_wp =
                                               let uu____10188 =
                                                 FStar_All.pipe_right md1
                                                   FStar_Syntax_Util.get_wp_ite_combinator in
                                               FStar_All.pipe_right
                                                 uu____10188 FStar_Util.must in
                                             let wp1 =
                                               let uu____10196 =
                                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                                   [u_res_t] env md1 ite_wp in
                                               let uu____10197 =
                                                 let uu____10198 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     res_t in
                                                 let uu____10207 =
                                                   let uu____10218 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp in
                                                   [uu____10218] in
                                                 uu____10198 :: uu____10207 in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu____10196 uu____10197
                                                 wp.FStar_Syntax_Syntax.pos in
                                             let uu____10251 =
                                               mk_comp md1 u_res_t res_t wp1
                                                 bind_cases_flags in
                                             (uu____10251, g_comp2)))))) in
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
          let uu____10285 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____10285 with
          | FStar_Pervasives_Native.None ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____10300 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c' in
                let uu____10305 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error uu____10300 uu____10305
              else
                (let uu____10313 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c' in
                 let uu____10318 = FStar_TypeChecker_Env.get_range env in
                 FStar_Errors.raise_error uu____10313 uu____10318)
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
          let uu____10342 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name in
          FStar_All.pipe_right uu____10342
            (FStar_TypeChecker_Env.norm_eff_name env) in
        let uu____10345 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid in
        if uu____10345
        then u_res
        else
          (let is_total =
             let uu____10348 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid in
             FStar_All.pipe_right uu____10348
               (FStar_List.existsb
                  (fun q -> q = FStar_Syntax_Syntax.TotalEffect)) in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____10356 = FStar_TypeChecker_Env.effect_repr env c u_res in
              match uu____10356 with
              | FStar_Pervasives_Native.None ->
                  let uu____10359 =
                    let uu____10364 =
                      let uu____10365 =
                        FStar_Syntax_Print.lid_to_string c_lid in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____10365 in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____10364) in
                  FStar_Errors.raise_error uu____10359
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
      let uu____10385 = destruct_wp_comp ct in
      match uu____10385 with
      | (u_t, t, wp) ->
          let vc =
            let uu____10402 =
              let uu____10403 =
                let uu____10404 =
                  FStar_All.pipe_right md
                    FStar_Syntax_Util.get_wp_trivial_combinator in
                FStar_All.pipe_right uu____10404 FStar_Util.must in
              FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                uu____10403 in
            let uu____10411 =
              let uu____10412 = FStar_Syntax_Syntax.as_arg t in
              let uu____10421 =
                let uu____10432 = FStar_Syntax_Syntax.as_arg wp in
                [uu____10432] in
              uu____10412 :: uu____10421 in
            let uu____10465 = FStar_TypeChecker_Env.get_range env in
            FStar_Syntax_Syntax.mk_Tm_app uu____10402 uu____10411 uu____10465 in
          let uu____10466 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc) in
          (ct, vc, uu____10466)
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
                  let uu____10520 =
                    FStar_TypeChecker_Env.try_lookup_lid env f in
                  match uu____10520 with
                  | FStar_Pervasives_Native.Some uu____10535 ->
                      ((let uu____10553 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions") in
                        if uu____10553
                        then
                          let uu____10554 = FStar_Ident.string_of_lid f in
                          FStar_Util.print1 "Coercing with %s!\n" uu____10554
                        else ());
                       (let coercion =
                          let uu____10557 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos in
                          FStar_Syntax_Syntax.fvar uu____10557
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs in
                        let lc1 =
                          let uu____10563 =
                            let uu____10564 =
                              let uu____10565 = mkcomp ty in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10565 in
                            (FStar_Pervasives_Native.None, uu____10564) in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____10563 in
                        let e1 =
                          let uu____10569 =
                            let uu____10570 = FStar_Syntax_Syntax.as_arg e in
                            [uu____10570] in
                          FStar_Syntax_Syntax.mk_Tm_app coercion2 uu____10569
                            e.FStar_Syntax_Syntax.pos in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None ->
                      ((let uu____10604 =
                          let uu____10609 =
                            let uu____10610 = FStar_Ident.string_of_lid f in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____10610 in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____10609) in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____10604);
                       (e, lc))
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee ->
    match projectee with | Yes _0 -> true | uu____10622 -> false
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee -> match projectee with | Yes _0 -> _0
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee ->
    match projectee with | Maybe -> true | uu____10634 -> false
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee -> match projectee with | No -> true | uu____10640 -> false
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
      let uu____10662 = FStar_Syntax_Util.head_and_args t2 in
      match uu____10662 with
      | (h, args) ->
          let h1 = FStar_Syntax_Util.un_uinst h in
          let r =
            let uu____10707 =
              let uu____10722 =
                let uu____10723 = FStar_Syntax_Subst.compress h1 in
                uu____10723.FStar_Syntax_Syntax.n in
              (uu____10722, args) in
            match uu____10707 with
            | (FStar_Syntax_Syntax.Tm_fvar fv,
               (a, FStar_Pervasives_Native.None)::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____10770, uu____10771) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown, uu____10804) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match (uu____10825, branches),
               uu____10827) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc ->
                        fun br ->
                          match acc with
                          | Yes uu____10891 -> Maybe
                          | Maybe -> Maybe
                          | No ->
                              let uu____10892 =
                                FStar_Syntax_Subst.open_branch br in
                              (match uu____10892 with
                               | (uu____10893, uu____10894, br_body) ->
                                   let uu____10912 =
                                     let uu____10913 =
                                       let uu____10918 =
                                         let uu____10919 =
                                           let uu____10922 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names in
                                           FStar_All.pipe_right uu____10922
                                             FStar_Util.set_elements in
                                         FStar_All.pipe_right uu____10919
                                           (FStar_TypeChecker_Env.push_bvs
                                              env) in
                                       check_erased uu____10918 in
                                     FStar_All.pipe_right br_body uu____10913 in
                                   (match uu____10912 with
                                    | No -> No
                                    | uu____10933 -> Maybe))) No)
            | uu____10934 -> No in
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
            (((let uu____10984 = FStar_Options.use_two_phase_tc () in
               Prims.op_Negation uu____10984) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ()) in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
               let uu____10999 =
                 let uu____11000 = FStar_Syntax_Subst.compress t1 in
                 uu____11000.FStar_Syntax_Syntax.n in
               match uu____10999 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____11004 -> false in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
               let uu____11012 =
                 let uu____11013 = FStar_Syntax_Subst.compress t1 in
                 uu____11013.FStar_Syntax_Syntax.n in
               match uu____11012 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____11017 -> false in
             let is_type t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
               let t2 = FStar_Syntax_Util.unrefine t1 in
               let uu____11026 =
                 let uu____11027 = FStar_Syntax_Subst.compress t2 in
                 uu____11027.FStar_Syntax_Syntax.n in
               match uu____11026 with
               | FStar_Syntax_Syntax.Tm_type uu____11030 -> true
               | uu____11031 -> false in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ in
             let uu____11033 = FStar_Syntax_Util.head_and_args res_typ in
             match uu____11033 with
             | (head, args) ->
                 ((let uu____11083 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions") in
                   if uu____11083
                   then
                     let uu____11084 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                     let uu____11085 = FStar_Syntax_Print.term_to_string e in
                     let uu____11086 =
                       FStar_Syntax_Print.term_to_string res_typ in
                     let uu____11087 =
                       FStar_Syntax_Print.term_to_string exp_t in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____11084 uu____11085 uu____11086 uu____11087
                   else ());
                  (let mk_erased u t =
                     let uu____11102 =
                       let uu____11105 =
                         fvar_const env FStar_Parser_Const.erased_lid in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____11105 [u] in
                     let uu____11106 =
                       let uu____11117 = FStar_Syntax_Syntax.as_arg t in
                       [uu____11117] in
                     FStar_Syntax_Util.mk_app uu____11102 uu____11106 in
                   let uu____11142 =
                     let uu____11157 =
                       let uu____11158 = FStar_Syntax_Util.un_uinst head in
                       uu____11158.FStar_Syntax_Syntax.n in
                     (uu____11157, args) in
                   match uu____11142 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type exp_t)
                       ->
                       let uu____11196 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total in
                       (match uu____11196 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____11236 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac in
                       (match uu____11236 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11276 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac in
                       (match uu____11276 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11316 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac in
                       (match uu____11316 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____11337 ->
                       let uu____11352 =
                         let uu____11357 = check_erased env res_typ in
                         let uu____11358 = check_erased env exp_t in
                         (uu____11357, uu____11358) in
                       (match uu____11352 with
                        | (No, Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty in
                            let uu____11367 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty in
                            (match uu____11367 with
                             | FStar_Pervasives_Native.None ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e in
                                 let uu____11378 =
                                   let uu____11383 =
                                     let uu____11384 =
                                       FStar_Syntax_Syntax.iarg ty in
                                     [uu____11384] in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____11383
                                     FStar_Syntax_Syntax.mk_Total in
                                 (match uu____11378 with
                                  | (e1, lc1) -> (e1, lc1, g1)))
                        | (Yes ty, No) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty in
                            let uu____11419 =
                              let uu____11424 =
                                let uu____11425 = FStar_Syntax_Syntax.iarg ty in
                                [uu____11425] in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____11424
                                FStar_Syntax_Syntax.mk_GTotal in
                            (match uu____11419 with
                             | (e1, lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____11458 ->
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
        let uu____11492 = FStar_Syntax_Util.head_and_args rt1 in
        match uu____11492 with
        | (hd, args) ->
            let uu____11541 =
              let uu____11556 =
                let uu____11557 = FStar_Syntax_Subst.compress hd in
                uu____11557.FStar_Syntax_Syntax.n in
              (uu____11556, args) in
            (match uu____11541 with
             | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____11595 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac in
                 FStar_All.pipe_left
                   (fun uu____11622 ->
                      FStar_Pervasives_Native.Some uu____11622) uu____11595
             | uu____11623 -> FStar_Pervasives_Native.None)
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
          (let uu____11675 =
             FStar_TypeChecker_Env.debug env FStar_Options.High in
           if uu____11675
           then
             let uu____11676 = FStar_Syntax_Print.term_to_string e in
             let uu____11677 = FStar_TypeChecker_Common.lcomp_to_string lc in
             let uu____11678 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____11676 uu____11677 uu____11678
           else ());
          (let use_eq =
             (env.FStar_TypeChecker_Env.use_eq_strict ||
                env.FStar_TypeChecker_Env.use_eq)
               ||
               (let uu____11684 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name in
                match uu____11684 with
                | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____11707 -> false) in
           let gopt =
             if use_eq
             then
               let uu____11729 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t in
               (uu____11729, false)
             else
               (let uu____11735 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t in
                (uu____11735, true)) in
           match gopt with
           | (FStar_Pervasives_Native.None, uu____11746) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____11755 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ in
                 FStar_Errors.raise_error uu____11755
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1419_11769 = lc in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1419_11769.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1419_11769.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1419_11769.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g, apply_guard) ->
               let uu____11774 = FStar_TypeChecker_Env.guard_form g in
               (match uu____11774 with
                | FStar_TypeChecker_Common.Trivial ->
                    let strengthen_trivial uu____11790 =
                      let uu____11791 =
                        FStar_TypeChecker_Common.lcomp_comp lc in
                      match uu____11791 with
                      | (c, g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c in
                          let set_result_typ c1 =
                            FStar_Syntax_Util.set_result_typ c1 t in
                          let uu____11811 =
                            let uu____11812 = FStar_Syntax_Util.eq_tm t res_t in
                            uu____11812 = FStar_Syntax_Util.Equal in
                          if uu____11811
                          then
                            ((let uu____11818 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____11818
                              then
                                let uu____11819 =
                                  FStar_Syntax_Print.term_to_string res_t in
                                let uu____11820 =
                                  FStar_Syntax_Print.term_to_string t in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____11819 uu____11820
                              else ());
                             (let uu____11822 = set_result_typ c in
                              (uu____11822, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____11826 ->
                                   true
                               | uu____11833 -> false in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t in
                               let uu____11839 =
                                 let uu____11844 =
                                   let uu____11845 =
                                     FStar_All.pipe_right c
                                       FStar_Syntax_Util.comp_effect_name in
                                   FStar_All.pipe_right uu____11845
                                     (FStar_TypeChecker_Env.norm_eff_name env) in
                                 let uu____11848 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env uu____11844
                                   (comp_univ_opt c) res_t uu____11848 in
                               match uu____11839 with
                               | (cret, gret) ->
                                   let lc1 =
                                     let uu____11858 =
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                         c in
                                     let uu____11859 =
                                       let uu____11860 =
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                           cret in
                                       ((FStar_Pervasives_Native.Some x),
                                         uu____11860) in
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (FStar_Pervasives_Native.Some e)
                                       uu____11858 uu____11859 in
                                   ((let uu____11864 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme in
                                     if uu____11864
                                     then
                                       let uu____11865 =
                                         FStar_Syntax_Print.term_to_string e in
                                       let uu____11866 =
                                         FStar_Syntax_Print.comp_to_string c in
                                       let uu____11867 =
                                         FStar_Syntax_Print.term_to_string t in
                                       let uu____11868 =
                                         FStar_TypeChecker_Common.lcomp_to_string
                                           lc1 in
                                       FStar_Util.print4
                                         "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                         uu____11865 uu____11866 uu____11867
                                         uu____11868
                                     else ());
                                    (let uu____11870 =
                                       FStar_TypeChecker_Common.lcomp_comp
                                         lc1 in
                                     match uu____11870 with
                                     | (c1, g_lc) ->
                                         let uu____11881 = set_result_typ c1 in
                                         let uu____11882 =
                                           FStar_TypeChecker_Env.conj_guards
                                             [g_c; gret; g_lc] in
                                         (uu____11881, uu____11882)))
                             else
                               ((let uu____11885 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____11885
                                 then
                                   let uu____11886 =
                                     FStar_Syntax_Print.term_to_string res_t in
                                   let uu____11887 =
                                     FStar_Syntax_Print.comp_to_string c in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____11886 uu____11887
                                 else ());
                                (let uu____11889 = set_result_typ c in
                                 (uu____11889, g_c)))) in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1458_11893 = g in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred_to_tac =
                          (uu___1458_11893.FStar_TypeChecker_Common.deferred_to_tac);
                        FStar_TypeChecker_Common.deferred =
                          (uu___1458_11893.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1458_11893.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1458_11893.FStar_TypeChecker_Common.implicits)
                      } in
                    let strengthen uu____11903 =
                      let uu____11904 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ()) in
                      if uu____11904
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f in
                         let uu____11911 =
                           let uu____11912 = FStar_Syntax_Subst.compress f1 in
                           uu____11912.FStar_Syntax_Syntax.n in
                         match uu____11911 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____11919,
                              {
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Tm_fvar fv;
                                FStar_Syntax_Syntax.pos = uu____11921;
                                FStar_Syntax_Syntax.vars = uu____11922;_},
                              uu____11923)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1474_11949 = lc in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1474_11949.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1474_11949.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1474_11949.FStar_TypeChecker_Common.comp_thunk)
                               } in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____11950 ->
                             let uu____11951 =
                               FStar_TypeChecker_Common.lcomp_comp lc in
                             (match uu____11951 with
                              | (c, g_c) ->
                                  ((let uu____11963 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme in
                                    if uu____11963
                                    then
                                      let uu____11964 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ in
                                      let uu____11965 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t in
                                      let uu____11966 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c in
                                      let uu____11967 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1 in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____11964 uu____11965 uu____11966
                                        uu____11967
                                    else ());
                                   (let u_t_opt = comp_univ_opt c in
                                    let x =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (t.FStar_Syntax_Syntax.pos)) t in
                                    let xexp =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____11974 =
                                      let uu____11979 =
                                        let uu____11980 =
                                          FStar_All.pipe_right c
                                            FStar_Syntax_Util.comp_effect_name in
                                        FStar_All.pipe_right uu____11980
                                          (FStar_TypeChecker_Env.norm_eff_name
                                             env) in
                                      return_value env uu____11979 u_t_opt t
                                        xexp in
                                    match uu____11974 with
                                    | (cret, gret) ->
                                        let guard =
                                          if apply_guard
                                          then
                                            let uu____11990 =
                                              let uu____11991 =
                                                FStar_Syntax_Syntax.as_arg
                                                  xexp in
                                              [uu____11991] in
                                            FStar_Syntax_Syntax.mk_Tm_app f1
                                              uu____11990
                                              f1.FStar_Syntax_Syntax.pos
                                          else f1 in
                                        let uu____12017 =
                                          let uu____12022 =
                                            FStar_All.pipe_left
                                              (fun uu____12039 ->
                                                 FStar_Pervasives_Native.Some
                                                   uu____12039)
                                              (FStar_TypeChecker_Err.subtyping_failed
                                                 env
                                                 lc.FStar_TypeChecker_Common.res_typ
                                                 t) in
                                          let uu____12040 =
                                            let uu____12041 =
                                              FStar_TypeChecker_Env.push_bvs
                                                env [x] in
                                            FStar_TypeChecker_Env.set_range
                                              uu____12041
                                              e.FStar_Syntax_Syntax.pos in
                                          let uu____12042 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              cret in
                                          let uu____12043 =
                                            FStar_All.pipe_left
                                              FStar_TypeChecker_Env.guard_of_guard_formula
                                              (FStar_TypeChecker_Common.NonTrivial
                                                 guard) in
                                          strengthen_precondition uu____12022
                                            uu____12040 e uu____12042
                                            uu____12043 in
                                        (match uu____12017 with
                                         | (eq_ret,
                                            _trivial_so_ok_to_discard) ->
                                             let x1 =
                                               let uu___1494_12051 = x in
                                               {
                                                 FStar_Syntax_Syntax.ppname =
                                                   (uu___1494_12051.FStar_Syntax_Syntax.ppname);
                                                 FStar_Syntax_Syntax.index =
                                                   (uu___1494_12051.FStar_Syntax_Syntax.index);
                                                 FStar_Syntax_Syntax.sort =
                                                   (lc.FStar_TypeChecker_Common.res_typ)
                                               } in
                                             let c1 =
                                               let uu____12053 =
                                                 FStar_TypeChecker_Common.lcomp_of_comp
                                                   c in
                                               bind e.FStar_Syntax_Syntax.pos
                                                 env
                                                 (FStar_Pervasives_Native.Some
                                                    e) uu____12053
                                                 ((FStar_Pervasives_Native.Some
                                                     x1), eq_ret) in
                                             let uu____12056 =
                                               FStar_TypeChecker_Common.lcomp_comp
                                                 c1 in
                                             (match uu____12056 with
                                              | (c2, g_lc) ->
                                                  ((let uu____12068 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        FStar_Options.Extreme in
                                                    if uu____12068
                                                    then
                                                      let uu____12069 =
                                                        FStar_TypeChecker_Normalize.comp_to_string
                                                          env c2 in
                                                      FStar_Util.print1
                                                        "Strengthened to %s\n"
                                                        uu____12069
                                                    else ());
                                                   (let uu____12071 =
                                                      FStar_TypeChecker_Env.conj_guards
                                                        [g_c; gret; g_lc] in
                                                    (c2, uu____12071))))))))) in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_12080 ->
                              match uu___6_12080 with
                              | FStar_Syntax_Syntax.RETURN ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____12083 -> [])) in
                    let lc1 =
                      let uu____12085 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name in
                      FStar_TypeChecker_Common.mk_lcomp uu____12085 t flags
                        strengthen in
                    let g2 =
                      let uu___1510_12087 = g1 in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred_to_tac =
                          (uu___1510_12087.FStar_TypeChecker_Common.deferred_to_tac);
                        FStar_TypeChecker_Common.deferred =
                          (uu___1510_12087.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1510_12087.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1510_12087.FStar_TypeChecker_Common.implicits)
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
        let uu____12122 =
          let uu____12125 =
            let uu____12126 =
              let uu____12135 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_Syntax_Syntax.as_arg uu____12135 in
            [uu____12126] in
          FStar_Syntax_Syntax.mk_Tm_app ens uu____12125
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____12122 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t in
      let uu____12158 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____12158
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____12174 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____12189 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____12205 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid) in
             if uu____12205
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req, uu____12219)::(ens, uu____12221)::uu____12222 ->
                    let uu____12265 =
                      let uu____12268 = norm req in
                      FStar_Pervasives_Native.Some uu____12268 in
                    let uu____12269 =
                      let uu____12270 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____12270 in
                    (uu____12265, uu____12269)
                | uu____12273 ->
                    let uu____12284 =
                      let uu____12289 =
                        let uu____12290 =
                          FStar_Syntax_Print.comp_to_string comp in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____12290 in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____12289) in
                    FStar_Errors.raise_error uu____12284
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp, uu____12306)::uu____12307 ->
                    let uu____12334 =
                      let uu____12339 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____12339 in
                    (match uu____12334 with
                     | (us_r, uu____12371) ->
                         let uu____12372 =
                           let uu____12377 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____12377 in
                         (match uu____12372 with
                          | (us_e, uu____12409) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____12412 =
                                  let uu____12413 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r in
                                  FStar_Syntax_Syntax.fvar uu____12413
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12412
                                  us_r in
                              let as_ens =
                                let uu____12415 =
                                  let uu____12416 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r in
                                  FStar_Syntax_Syntax.fvar uu____12416
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12415
                                  us_e in
                              let req =
                                let uu____12418 =
                                  let uu____12419 =
                                    let uu____12430 =
                                      FStar_Syntax_Syntax.as_arg wp in
                                    [uu____12430] in
                                  ((ct1.FStar_Syntax_Syntax.result_typ),
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.imp_tag))
                                    :: uu____12419 in
                                FStar_Syntax_Syntax.mk_Tm_app as_req
                                  uu____12418
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____12468 =
                                  let uu____12469 =
                                    let uu____12480 =
                                      FStar_Syntax_Syntax.as_arg wp in
                                    [uu____12480] in
                                  ((ct1.FStar_Syntax_Syntax.result_typ),
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.imp_tag))
                                    :: uu____12469 in
                                FStar_Syntax_Syntax.mk_Tm_app as_ens
                                  uu____12468
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____12517 =
                                let uu____12520 = norm req in
                                FStar_Pervasives_Native.Some uu____12520 in
                              let uu____12521 =
                                let uu____12522 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____12522 in
                              (uu____12517, uu____12521)))
                | uu____12525 -> failwith "Impossible"))
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
        (let uu____12562 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____12562
         then
           let uu____12563 = FStar_Syntax_Print.term_to_string tm in
           let uu____12564 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____12563
             uu____12564
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
          (let uu____12619 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify") in
           if uu____12619
           then
             let uu____12620 = FStar_Syntax_Print.term_to_string tm in
             let uu____12621 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____12620
               uu____12621
           else ());
          tm'
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____12628 =
      let uu____12629 =
        let uu____12630 = FStar_Syntax_Subst.compress t in
        uu____12630.FStar_Syntax_Syntax.n in
      match uu____12629 with
      | FStar_Syntax_Syntax.Tm_app uu____12633 -> false
      | uu____12650 -> true in
    if uu____12628
    then t
    else
      (let uu____12652 = FStar_Syntax_Util.head_and_args t in
       match uu____12652 with
       | (head, args) ->
           let uu____12695 =
             let uu____12696 =
               let uu____12697 = FStar_Syntax_Subst.compress head in
               uu____12697.FStar_Syntax_Syntax.n in
             match uu____12696 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) ->
                 true
             | uu____12700 -> false in
           if uu____12695
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____12730 ->
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
          ((let uu____12772 =
              FStar_TypeChecker_Env.debug env FStar_Options.High in
            if uu____12772
            then
              let uu____12773 = FStar_Syntax_Print.term_to_string e in
              let uu____12774 = FStar_Syntax_Print.term_to_string t in
              let uu____12775 =
                let uu____12776 = FStar_TypeChecker_Env.expected_typ env in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____12776 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____12773 uu____12774 uu____12775
            else ());
           (let unfolded_arrow_formals t1 =
              let rec aux bs t2 =
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf env t2 in
                let uu____12810 = FStar_Syntax_Util.arrow_formals t3 in
                match uu____12810 with
                | (bs', t4) ->
                    (match bs' with
                     | [] -> bs
                     | bs'1 -> aux (FStar_List.append bs bs'1) t4) in
              aux [] t1 in
            let number_of_implicits t1 =
              let formals = unfolded_arrow_formals t1 in
              let n_implicits =
                let uu____12844 =
                  FStar_All.pipe_right formals
                    (FStar_Util.prefix_until
                       (fun uu____12922 ->
                          match uu____12922 with
                          | (uu____12929, imp) ->
                              (FStar_Option.isNone imp) ||
                                (let uu____12936 =
                                   FStar_Syntax_Util.eq_aqual imp
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Equality) in
                                 uu____12936 = FStar_Syntax_Util.Equal))) in
                match uu____12844 with
                | FStar_Pervasives_Native.None -> FStar_List.length formals
                | FStar_Pervasives_Native.Some
                    (implicits, _first_explicit, _rest) ->
                    FStar_List.length implicits in
              n_implicits in
            let inst_n_binders t1 =
              let uu____13054 = FStar_TypeChecker_Env.expected_typ env in
              match uu____13054 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t in
                  let n_available = number_of_implicits t1 in
                  if n_available < n_expected
                  then
                    let uu____13064 =
                      let uu____13069 =
                        let uu____13070 = FStar_Util.string_of_int n_expected in
                        let uu____13071 = FStar_Syntax_Print.term_to_string e in
                        let uu____13072 =
                          FStar_Util.string_of_int n_available in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____13070 uu____13071 uu____13072 in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____13069) in
                    let uu____13073 = FStar_TypeChecker_Env.get_range env in
                    FStar_Errors.raise_error uu____13064 uu____13073
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected) in
            let decr_inst uu___7_13086 =
              match uu___7_13086 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one) in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                let uu____13121 = FStar_Syntax_Subst.open_comp bs c in
                (match uu____13121 with
                 | (bs1, c1) ->
                     let rec aux subst inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some uu____13247,
                          uu____13236) when uu____13247 = Prims.int_zero ->
                           ([], bs2, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____13280,
                          (x, FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit uu____13282))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort in
                           let uu____13313 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2 in
                           (match uu____13313 with
                            | (v, uu____13353, g) ->
                                ((let uu____13368 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High in
                                  if uu____13368
                                  then
                                    let uu____13369 =
                                      FStar_Syntax_Print.term_to_string v in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____13369
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst in
                                  let uu____13376 =
                                    aux subst1 (decr_inst inst_n) rest in
                                  match uu____13376 with
                                  | (args, bs3, subst2, g') ->
                                      let uu____13469 =
                                        FStar_TypeChecker_Env.conj_guard g g' in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____13469))))
                       | (uu____13496,
                          (x, FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tac_or_attr))::rest) ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort in
                           let meta_t =
                             match tac_or_attr with
                             | FStar_Syntax_Syntax.Arg_qualifier_meta_tac tau
                                 ->
                                 let uu____13533 =
                                   let uu____13540 = FStar_Dyn.mkdyn env in
                                   (uu____13540, tau) in
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   uu____13533
                             | FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                 attr ->
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_attr attr in
                           let uu____13546 =
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict
                               (FStar_Pervasives_Native.Some meta_t) in
                           (match uu____13546 with
                            | (v, uu____13586, g) ->
                                ((let uu____13601 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High in
                                  if uu____13601
                                  then
                                    let uu____13602 =
                                      FStar_Syntax_Print.term_to_string v in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____13602
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst in
                                  let uu____13609 =
                                    aux subst1 (decr_inst inst_n) rest in
                                  match uu____13609 with
                                  | (args, bs3, subst2, g') ->
                                      let uu____13702 =
                                        FStar_TypeChecker_Env.conj_guard g g' in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____13702))))
                       | (uu____13729, bs3) ->
                           ([], bs3, subst,
                             FStar_TypeChecker_Env.trivial_guard) in
                     let uu____13775 =
                       let uu____13802 = inst_n_binders t1 in
                       aux [] uu____13802 bs1 in
                     (match uu____13775 with
                      | (args, bs2, subst, guard) ->
                          (match (args, bs2) with
                           | ([], uu____13873) -> (e, torig, guard)
                           | (uu____13904, []) when
                               let uu____13935 =
                                 FStar_Syntax_Util.is_total_comp c1 in
                               Prims.op_Negation uu____13935 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____13936 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____13964 ->
                                     FStar_Syntax_Util.arrow bs2 c1 in
                               let t3 = FStar_Syntax_Subst.subst subst t2 in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   e.FStar_Syntax_Syntax.pos in
                               (e1, t3, guard))))
            | uu____13975 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs ->
    let uu____13985 =
      let uu____13988 = FStar_Util.set_elements univs in
      FStar_All.pipe_right uu____13988
        (FStar_List.map
           (fun u ->
              let uu____13998 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____13998 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____13985 (FStar_String.concat ", ")
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env ->
    fun x ->
      let uu____14019 = FStar_Util.set_is_empty x in
      if uu____14019
      then []
      else
        (let s =
           let uu____14036 =
             let uu____14039 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____14039 in
           FStar_All.pipe_right uu____14036 FStar_Util.set_elements in
         (let uu____14057 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____14057
          then
            let uu____14058 =
              let uu____14059 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____14059 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____14058
          else ());
         (let r =
            let uu____14066 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____14066 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____14111 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____14111
                     then
                       let uu____14112 =
                         let uu____14113 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____14113 in
                       let uu____14114 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____14115 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____14112 uu____14114 uu____14115
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
        let uu____14141 =
          FStar_Util.set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____14141 FStar_Util.set_elements in
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
        | ([], uu____14179) -> generalized_univ_names
        | (uu____14186, []) -> explicit_univ_names
        | uu____14193 ->
            let uu____14202 =
              let uu____14207 =
                let uu____14208 = FStar_Syntax_Print.term_to_string t in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____14208 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____14207) in
            FStar_Errors.raise_error uu____14202 t.FStar_Syntax_Syntax.pos
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
      (let uu____14226 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____14226
       then
         let uu____14227 = FStar_Syntax_Print.term_to_string t in
         let uu____14228 = FStar_Syntax_Print.univ_names_to_string univnames in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____14227 uu____14228
       else ());
      (let univs = FStar_Syntax_Free.univs t in
       (let uu____14234 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____14234
        then
          let uu____14235 = string_of_univs univs in
          FStar_Util.print1 "univs to gen : %s\n" uu____14235
        else ());
       (let gen = gen_univs env univs in
        (let uu____14241 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen") in
         if uu____14241
         then
           let uu____14242 = FStar_Syntax_Print.term_to_string t in
           let uu____14243 = FStar_Syntax_Print.univ_names_to_string gen in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____14242 uu____14243
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
        let uu____14321 =
          let uu____14322 =
            FStar_Util.for_all
              (fun uu____14335 ->
                 match uu____14335 with
                 | (uu____14344, uu____14345, c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          FStar_All.pipe_left Prims.op_Negation uu____14322 in
        if uu____14321
        then FStar_Pervasives_Native.None
        else
          (let norm c =
             (let uu____14393 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              if uu____14393
              then
                let uu____14394 = FStar_Syntax_Print.comp_to_string c in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____14394
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c in
              (let uu____14398 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____14398
               then
                 let uu____14399 = FStar_Syntax_Print.comp_to_string c1 in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____14399
               else ());
              c1) in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu____14414 = FStar_Util.set_difference uvs env_uvars in
             FStar_All.pipe_right uu____14414 FStar_Util.set_elements in
           let univs_and_uvars_of_lec uu____14448 =
             match uu____14448 with
             | (lbname, e, c) ->
                 let c1 = norm c in
                 let t = FStar_Syntax_Util.comp_result c1 in
                 let univs = FStar_Syntax_Free.univs t in
                 let uvt = FStar_Syntax_Free.uvars t in
                 ((let uu____14485 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen") in
                   if uu____14485
                   then
                     let uu____14486 =
                       let uu____14487 =
                         let uu____14490 = FStar_Util.set_elements univs in
                         FStar_All.pipe_right uu____14490
                           (FStar_List.map
                              (fun u ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u))) in
                       FStar_All.pipe_right uu____14487
                         (FStar_String.concat ", ") in
                     let uu____14541 =
                       let uu____14542 =
                         let uu____14545 = FStar_Util.set_elements uvt in
                         FStar_All.pipe_right uu____14545
                           (FStar_List.map
                              (fun u ->
                                 let uu____14556 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head in
                                 let uu____14557 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                 FStar_Util.format2 "(%s : %s)" uu____14556
                                   uu____14557)) in
                       FStar_All.pipe_right uu____14542
                         (FStar_String.concat ", ") in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____14486
                       uu____14541
                   else ());
                  (let univs1 =
                     let uu____14564 = FStar_Util.set_elements uvt in
                     FStar_List.fold_left
                       (fun univs1 ->
                          fun uv ->
                            let uu____14576 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ in
                            FStar_Util.set_union univs1 uu____14576) univs
                       uu____14564 in
                   let uvs = gen_uvars uvt in
                   (let uu____14583 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen") in
                    if uu____14583
                    then
                      let uu____14584 =
                        let uu____14585 =
                          let uu____14588 = FStar_Util.set_elements univs1 in
                          FStar_All.pipe_right uu____14588
                            (FStar_List.map
                               (fun u ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u))) in
                        FStar_All.pipe_right uu____14585
                          (FStar_String.concat ", ") in
                      let uu____14639 =
                        let uu____14640 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u ->
                                  let uu____14651 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head in
                                  let uu____14652 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                  FStar_Util.format2 "(%s : %s)" uu____14651
                                    uu____14652)) in
                        FStar_All.pipe_right uu____14640
                          (FStar_String.concat ", ") in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____14584 uu____14639
                    else ());
                   (univs1, uvs, (lbname, e, c1)))) in
           let uu____14666 =
             let uu____14683 = FStar_List.hd lecs in
             univs_and_uvars_of_lec uu____14683 in
           match uu____14666 with
           | (univs, uvs, lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____14773 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1) in
                 if uu____14773
                 then ()
                 else
                   (let uu____14775 = lec_hd in
                    match uu____14775 with
                    | (lb1, uu____14783, uu____14784) ->
                        let uu____14785 = lec2 in
                        (match uu____14785 with
                         | (lb2, uu____14793, uu____14794) ->
                             let msg =
                               let uu____14796 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____14797 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____14796 uu____14797 in
                             let uu____14798 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____14798)) in
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
                 let uu____14862 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1) in
                 if uu____14862
                 then ()
                 else
                   (let uu____14864 = lec_hd in
                    match uu____14864 with
                    | (lb1, uu____14872, uu____14873) ->
                        let uu____14874 = lec2 in
                        (match uu____14874 with
                         | (lb2, uu____14882, uu____14883) ->
                             let msg =
                               let uu____14885 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____14886 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____14885 uu____14886 in
                             let uu____14887 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____14887)) in
               let lecs1 =
                 let uu____14897 = FStar_List.tl lecs in
                 FStar_List.fold_right
                   (fun this_lec ->
                      fun lecs1 ->
                        let uu____14950 = univs_and_uvars_of_lec this_lec in
                        match uu____14950 with
                        | (this_univs, this_uvs, this_lec1) ->
                            (force_univs_eq this_lec1 univs this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____14897 [] in
               let lecs2 = lec_hd :: lecs1 in
               let gen_types uvs1 =
                 let fail rng k =
                   let uu____15060 = lec_hd in
                   match uu____15060 with
                   | (lbname, e, c) ->
                       let uu____15070 =
                         let uu____15075 =
                           let uu____15076 =
                             FStar_Syntax_Print.term_to_string k in
                           let uu____15077 =
                             FStar_Syntax_Print.lbname_to_string lbname in
                           let uu____15078 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c) in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____15076 uu____15077 uu____15078 in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____15075) in
                       FStar_Errors.raise_error uu____15070 rng in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u ->
                         let uu____15097 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head in
                         match uu____15097 with
                         | FStar_Pervasives_Native.Some uu____15106 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____15113 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ in
                             let uu____15117 =
                               FStar_Syntax_Util.arrow_formals k in
                             (match uu____15117 with
                              | (bs, kres) ->
                                  ((let uu____15137 =
                                      let uu____15138 =
                                        let uu____15141 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres in
                                        FStar_Syntax_Util.unrefine
                                          uu____15141 in
                                      uu____15138.FStar_Syntax_Syntax.n in
                                    match uu____15137 with
                                    | FStar_Syntax_Syntax.Tm_type uu____15142
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres in
                                        let uu____15146 =
                                          let uu____15147 =
                                            FStar_Util.set_is_empty free in
                                          Prims.op_Negation uu____15147 in
                                        if uu____15146
                                        then
                                          fail
                                            u.FStar_Syntax_Syntax.ctx_uvar_range
                                            kres
                                        else ()
                                    | uu____15149 ->
                                        fail
                                          u.FStar_Syntax_Syntax.ctx_uvar_range
                                          kres);
                                   (let a =
                                      let uu____15151 =
                                        let uu____15154 =
                                          FStar_TypeChecker_Env.get_range env in
                                        FStar_All.pipe_left
                                          (fun uu____15157 ->
                                             FStar_Pervasives_Native.Some
                                               uu____15157) uu____15154 in
                                      FStar_Syntax_Syntax.new_bv uu____15151
                                        kres in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____15165 ->
                                          let uu____15166 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Util.abs bs
                                            uu____15166
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
                      (fun uu____15269 ->
                         match uu____15269 with
                         | (lbname, e, c) ->
                             let uu____15315 =
                               match (gen_tvars, gen_univs1) with
                               | ([], []) -> (e, c, [])
                               | uu____15376 ->
                                   let uu____15389 = (e, c) in
                                   (match uu____15389 with
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
                                                (fun uu____15428 ->
                                                   match uu____15428 with
                                                   | (x, uu____15434) ->
                                                       let uu____15435 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____15435)
                                                gen_tvars in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____15453 =
                                                let uu____15454 =
                                                  FStar_Util.right lbname in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____15454 in
                                              if uu____15453
                                              then
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  tm tvar_args
                                                  tm.FStar_Syntax_Syntax.pos
                                              else tm in
                                            FStar_Syntax_InstFV.inst
                                              instantiate_lbname_with_app e1
                                          else e1 in
                                        let t =
                                          let uu____15460 =
                                            let uu____15461 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____15461.FStar_Syntax_Syntax.n in
                                          match uu____15460 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs, cod) ->
                                              let uu____15486 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____15486 with
                                               | (bs1, cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____15497 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____15501 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____15501, gen_tvars)) in
                             (match uu____15315 with
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
        (let uu____15645 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____15645
         then
           let uu____15646 =
             let uu____15647 =
               FStar_List.map
                 (fun uu____15660 ->
                    match uu____15660 with
                    | (lb, uu____15668, uu____15669) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_All.pipe_right uu____15647 (FStar_String.concat ", ") in
           FStar_Util.print1 "Generalizing: %s\n" uu____15646
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____15690 ->
                match uu____15690 with
                | (l, t, c) -> gather_free_univnames env t) lecs in
         let generalized_lecs =
           let uu____15719 = gen env is_rec lecs in
           match uu____15719 with
           | FStar_Pervasives_Native.None ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____15818 ->
                       match uu____15818 with
                       | (l, t, c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____15880 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 if uu____15880
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____15926 ->
                           match uu____15926 with
                           | (l, us, e, c, gvs) ->
                               let uu____15960 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos in
                               let uu____15961 =
                                 FStar_Syntax_Print.lbname_to_string l in
                               let uu____15962 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c) in
                               let uu____15963 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____15964 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____15960 uu____15961 uu____15962
                                 uu____15963 uu____15964))
                 else ());
                luecs) in
         FStar_List.map2
           (fun univnames ->
              fun uu____16005 ->
                match uu____16005 with
                | (l, generalized_univs, t, c, gvs) ->
                    let uu____16049 =
                      check_universe_generalization univnames
                        generalized_univs t in
                    (l, uu____16049, t, c, gvs)) univnames_lecs
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
        let uu____16101 =
          let uu____16104 =
            let uu____16105 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.string_of_lid uu____16105 in
          FStar_Pervasives_Native.Some uu____16104 in
        FStar_Profiling.profile
          (fun uu____16121 -> generalize' env is_rec lecs) uu____16101
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
              let uu____16175 =
                FStar_TypeChecker_Rel.get_teq_predicate env2 t1 t21 in
              match uu____16175 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some f ->
                  let uu____16181 = FStar_TypeChecker_Env.apply_guard f e in
                  FStar_All.pipe_right uu____16181
                    (fun uu____16184 ->
                       FStar_Pervasives_Native.Some uu____16184)
            else
              if env2.FStar_TypeChecker_Env.use_eq
              then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
              else
                (let uu____16189 =
                   FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21 in
                 match uu____16189 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some f ->
                     let uu____16195 = FStar_TypeChecker_Env.apply_guard f e in
                     FStar_All.pipe_left
                       (fun uu____16198 ->
                          FStar_Pervasives_Native.Some uu____16198)
                       uu____16195) in
          let uu____16199 = maybe_coerce_lc env1 e lc t2 in
          match uu____16199 with
          | (e1, lc1, g_c) ->
              let uu____16215 =
                check env1 lc1.FStar_TypeChecker_Common.res_typ t2 in
              (match uu____16215 with
               | FStar_Pervasives_Native.None ->
                   let uu____16224 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ in
                   let uu____16229 = FStar_TypeChecker_Env.get_range env1 in
                   FStar_Errors.raise_error uu____16224 uu____16229
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____16238 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____16238
                     then
                       let uu____16239 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____16239
                     else ());
                    (let uu____16241 = FStar_TypeChecker_Env.conj_guard g g_c in
                     (e1, lc1, uu____16241))))
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env ->
    fun g ->
      fun lc ->
        (let uu____16266 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium in
         if uu____16266
         then
           let uu____16267 = FStar_TypeChecker_Common.lcomp_to_string lc in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____16267
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
         let uu____16277 = FStar_TypeChecker_Common.lcomp_comp lc in
         match uu____16277 with
         | (c, g_c) ->
             let uu____16288 = FStar_TypeChecker_Common.is_total_lcomp lc in
             if uu____16288
             then
               let uu____16293 =
                 let uu____16294 = FStar_TypeChecker_Env.conj_guard g1 g_c in
                 discharge uu____16294 in
               (uu____16293, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] in
                let c1 =
                  let uu____16300 =
                    let uu____16301 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    FStar_All.pipe_right uu____16301
                      FStar_Syntax_Syntax.mk_Comp in
                  FStar_All.pipe_right uu____16300
                    (FStar_TypeChecker_Normalize.normalize_comp steps env) in
                let uu____16302 = check_trivial_precondition env c1 in
                match uu____16302 with
                | (ct, vc, g_pre) ->
                    ((let uu____16317 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification") in
                      if uu____16317
                      then
                        let uu____16318 =
                          FStar_Syntax_Print.term_to_string vc in
                        FStar_Util.print1 "top-level VC: %s\n" uu____16318
                      else ());
                     (let uu____16320 =
                        let uu____16321 =
                          let uu____16322 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre in
                          FStar_TypeChecker_Env.conj_guard g1 uu____16322 in
                        discharge uu____16321 in
                      let uu____16323 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp in
                      (uu____16320, uu____16323)))))
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head ->
    fun seen_args ->
      let short_bin_op f uu___8_16355 =
        match uu___8_16355 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst, uu____16365)::[] -> f fst
        | uu____16390 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____16401 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____16401
          (fun uu____16402 -> FStar_TypeChecker_Common.NonTrivial uu____16402) in
      let op_or_e e =
        let uu____16413 =
          let uu____16414 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____16414 in
        FStar_All.pipe_right uu____16413
          (fun uu____16417 -> FStar_TypeChecker_Common.NonTrivial uu____16417) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun uu____16424 -> FStar_TypeChecker_Common.NonTrivial uu____16424) in
      let op_or_t t =
        let uu____16435 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____16435
          (fun uu____16438 -> FStar_TypeChecker_Common.NonTrivial uu____16438) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun uu____16445 -> FStar_TypeChecker_Common.NonTrivial uu____16445) in
      let short_op_ite uu___9_16451 =
        match uu___9_16451 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard, uu____16461)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard, uu____16488)::[] ->
            let uu____16529 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____16529
              (fun uu____16530 ->
                 FStar_TypeChecker_Common.NonTrivial uu____16530)
        | uu____16531 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____16542 =
          let uu____16550 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____16550) in
        let uu____16558 =
          let uu____16568 =
            let uu____16576 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____16576) in
          let uu____16584 =
            let uu____16594 =
              let uu____16602 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____16602) in
            let uu____16610 =
              let uu____16620 =
                let uu____16628 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____16628) in
              let uu____16636 =
                let uu____16646 =
                  let uu____16654 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____16654) in
                [uu____16646; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____16620 :: uu____16636 in
            uu____16594 :: uu____16610 in
          uu____16568 :: uu____16584 in
        uu____16542 :: uu____16558 in
      match head.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____16716 =
            FStar_Util.find_map table
              (fun uu____16731 ->
                 match uu____16731 with
                 | (x, mk) ->
                     let uu____16748 = FStar_Ident.lid_equals x lid in
                     if uu____16748
                     then
                       let uu____16751 = mk seen_args in
                       FStar_Pervasives_Native.Some uu____16751
                     else FStar_Pervasives_Native.None) in
          (match uu____16716 with
           | FStar_Pervasives_Native.None -> FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____16754 -> FStar_TypeChecker_Common.Trivial
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l ->
    let uu____16760 =
      let uu____16761 = FStar_Syntax_Util.un_uinst l in
      uu____16761.FStar_Syntax_Syntax.n in
    match uu____16760 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____16765 -> false
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env ->
    fun bs ->
      let pos bs1 =
        match bs1 with
        | (hd, uu____16799)::uu____16800 ->
            FStar_Syntax_Syntax.range_of_bv hd
        | uu____16819 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____16828, FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____16829))::uu____16830 -> bs
      | uu____16847 ->
          let uu____16848 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____16848 with
           | FStar_Pervasives_Native.None -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____16852 =
                 let uu____16853 = FStar_Syntax_Subst.compress t in
                 uu____16853.FStar_Syntax_Syntax.n in
               (match uu____16852 with
                | FStar_Syntax_Syntax.Tm_arrow (bs', uu____16857) ->
                    let uu____16878 =
                      FStar_Util.prefix_until
                        (fun uu___10_16918 ->
                           match uu___10_16918 with
                           | (uu____16925, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____16926)) ->
                               false
                           | uu____16929 -> true) bs' in
                    (match uu____16878 with
                     | FStar_Pervasives_Native.None -> bs
                     | FStar_Pervasives_Native.Some
                         ([], uu____16964, uu____16965) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps, uu____17037, uu____17038) ->
                         let uu____17111 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____17130 ->
                                   match uu____17130 with
                                   | (x, uu____17138) ->
                                       let uu____17143 =
                                         FStar_Ident.string_of_id
                                           x.FStar_Syntax_Syntax.ppname in
                                       FStar_Util.starts_with uu____17143 "'")) in
                         if uu____17111
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____17186 ->
                                     match uu____17186 with
                                     | (x, i) ->
                                         let uu____17205 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____17205, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____17215 -> bs))
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
            let uu____17243 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1)) in
            if uu____17243
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
          let uu____17270 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____17270
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
        (let uu____17305 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____17305
         then
           ((let uu____17307 = FStar_Ident.string_of_lid lident in
             d uu____17307);
            (let uu____17308 = FStar_Ident.string_of_lid lident in
             let uu____17309 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____17308 uu____17309))
         else ());
        (let fv =
           let uu____17312 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____17312
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
         let uu____17322 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Range.dummyRange in
         ((let uu___2137_17324 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2137_17324.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2137_17324.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2137_17324.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2137_17324.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2137_17324.FStar_Syntax_Syntax.sigopts)
           }), uu____17322))
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env ->
    fun se ->
      let visibility uu___11_17340 =
        match uu___11_17340 with
        | FStar_Syntax_Syntax.Private -> true
        | uu____17341 -> false in
      let reducibility uu___12_17347 =
        match uu___12_17347 with
        | FStar_Syntax_Syntax.Abstract -> true
        | FStar_Syntax_Syntax.Irreducible -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> true
        | FStar_Syntax_Syntax.Visible_default -> true
        | FStar_Syntax_Syntax.Inline_for_extraction -> true
        | uu____17348 -> false in
      let assumption uu___13_17354 =
        match uu___13_17354 with
        | FStar_Syntax_Syntax.Assumption -> true
        | FStar_Syntax_Syntax.New -> true
        | uu____17355 -> false in
      let reification uu___14_17361 =
        match uu___14_17361 with
        | FStar_Syntax_Syntax.Reifiable -> true
        | FStar_Syntax_Syntax.Reflectable uu____17362 -> true
        | uu____17363 -> false in
      let inferred uu___15_17369 =
        match uu___15_17369 with
        | FStar_Syntax_Syntax.Discriminator uu____17370 -> true
        | FStar_Syntax_Syntax.Projector uu____17371 -> true
        | FStar_Syntax_Syntax.RecordType uu____17376 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____17385 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor -> true
        | FStar_Syntax_Syntax.HasMaskedEffect -> true
        | FStar_Syntax_Syntax.Effect -> true
        | uu____17394 -> false in
      let has_eq uu___16_17400 =
        match uu___16_17400 with
        | FStar_Syntax_Syntax.Noeq -> true
        | FStar_Syntax_Syntax.Unopteq -> true
        | uu____17401 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____17465 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private -> true
        | uu____17470 -> true in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1 in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l ->
                  let uu____17500 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l in
                  FStar_Option.isSome uu____17500)) in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____17529 = FStar_Option.get attrs_opt in
                     FStar_Syntax_Util.has_attribute uu____17529
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
           | FStar_Syntax_Syntax.Sig_bundle uu____17539 ->
               let uu____17548 =
                 let uu____17549 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_17553 ->
                           match uu___17_17553 with
                           | FStar_Syntax_Syntax.Noeq -> true
                           | uu____17554 -> false)) in
                 Prims.op_Negation uu____17549 in
               if uu____17548
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____17556 -> ()
           | FStar_Syntax_Syntax.Sig_fail uu____17563 -> ()
           | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu____17575) ->
               let uu____17582 =
                 FStar_Syntax_Util.abs_formals lb.FStar_Syntax_Syntax.lbdef in
               (match uu____17582 with
                | (uu____17591, body, uu____17593) ->
                    let uu____17598 =
                      let uu____17599 =
                        FStar_TypeChecker_Normalize.non_info_norm env body in
                      Prims.op_Negation uu____17599 in
                    if uu____17598
                    then
                      let uu____17600 =
                        let uu____17605 =
                          let uu____17606 =
                            FStar_Syntax_Print.term_to_string body in
                          FStar_Util.format1
                            "Illegal attribute: the `erasable` attribute is only permitted on inductive type definitions and abbreviations for non-informative types. %s is considered informative."
                            uu____17606 in
                        (FStar_Errors.Fatal_QulifierListNotPermitted,
                          uu____17605) in
                      FStar_Errors.raise_error uu____17600
                        body.FStar_Syntax_Syntax.pos
                    else ())
           | uu____17608 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_QulifierListNotPermitted,
                   "Illegal attribute: the `erasable` attribute is only permitted on inductive type definitions and abbreviations for non-informative types")
                 r)
        else () in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic))) in
      let uu____17619 =
        let uu____17620 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_17624 ->
                  match uu___18_17624 with
                  | FStar_Syntax_Syntax.OnlyName -> true
                  | uu____17625 -> false)) in
        FStar_All.pipe_right uu____17620 Prims.op_Negation in
      if uu____17619
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x -> fun y -> x = y) quals in
        let err' msg =
          let uu____17640 =
            let uu____17645 =
              let uu____17646 = FStar_Syntax_Print.quals_to_string quals in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____17646 msg in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____17645) in
          FStar_Errors.raise_error uu____17640 r in
        let err msg = err' (Prims.op_Hat ": " msg) in
        let err'1 uu____17658 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____17662 =
            let uu____17663 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____17663 in
          if uu____17662 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec, uu____17669), uu____17670)
              ->
              ((let uu____17680 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____17680
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____17684 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x -> (assumption x) || (has_eq x))) in
                if uu____17684
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____17690 ->
              ((let uu____17700 =
                  let uu____17701 =
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
                  Prims.op_Negation uu____17701 in
                if uu____17700 then err'1 () else ());
               (let uu____17707 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_17711 ->
                           match uu___19_17711 with
                           | FStar_Syntax_Syntax.Unopteq -> true
                           | uu____17712 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr) in
                if uu____17707
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____17714 ->
              let uu____17721 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____17721 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____17725 ->
              let uu____17732 =
                let uu____17733 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____17733 in
              if uu____17732 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____17739 ->
              let uu____17740 =
                let uu____17741 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____17741 in
              if uu____17740 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____17747 ->
              let uu____17760 =
                let uu____17761 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____17761 in
              if uu____17760 then err'1 () else ()
          | uu____17767 -> ()))
      else ()
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g ->
    fun t ->
      let rec descend env t1 =
        let uu____17801 =
          let uu____17802 = FStar_Syntax_Subst.compress t1 in
          uu____17802.FStar_Syntax_Syntax.n in
        match uu____17801 with
        | FStar_Syntax_Syntax.Tm_arrow uu____17805 ->
            let uu____17820 = FStar_Syntax_Util.arrow_formals_comp t1 in
            (match uu____17820 with
             | (bs, c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____17828;
               FStar_Syntax_Syntax.index = uu____17829;
               FStar_Syntax_Syntax.sort = t2;_},
             uu____17831)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head, uu____17839) -> descend env head
        | FStar_Syntax_Syntax.Tm_uinst (head, uu____17865) ->
            descend env head
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____17871 -> false
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
        (let uu____17879 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction") in
         if uu____17879
         then
           let uu____17880 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____17880
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
                  let uu____17936 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t in
                  FStar_Errors.raise_error uu____17936 r in
                let uu____17945 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts in
                match uu____17945 with
                | (uu____17954, signature) ->
                    let uu____17956 =
                      let uu____17957 = FStar_Syntax_Subst.compress signature in
                      uu____17957.FStar_Syntax_Syntax.n in
                    (match uu____17956 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs, uu____17965) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____18013 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b ->
                                     let uu____18029 =
                                       FStar_Syntax_Print.binder_to_string b in
                                     let uu____18030 =
                                       FStar_Ident.string_of_lid eff_name in
                                     let uu____18031 =
                                       FStar_Range.string_of_range r in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____18029 uu____18030 uu____18031) r in
                              (match uu____18013 with
                               | (is, g) ->
                                   let uu____18042 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None ->
                                         let eff_c =
                                           let uu____18044 =
                                             let uu____18045 =
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
                                                 = uu____18045;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____18044 in
                                         let uu____18064 =
                                           let uu____18065 =
                                             let uu____18080 =
                                               let uu____18089 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   FStar_Syntax_Syntax.t_unit in
                                               [uu____18089] in
                                             (uu____18080, eff_c) in
                                           FStar_Syntax_Syntax.Tm_arrow
                                             uu____18065 in
                                         FStar_Syntax_Syntax.mk uu____18064 r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____18120 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u] in
                                           FStar_All.pipe_right uu____18120
                                             FStar_Pervasives_Native.snd in
                                         let uu____18129 =
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg (a_tm
                                             :: is) in
                                         FStar_Syntax_Syntax.mk_Tm_app repr
                                           uu____18129 r in
                                   (uu____18042, g))
                          | uu____18138 -> fail signature)
                     | uu____18139 -> fail signature)
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
            let uu____18169 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env) in
            FStar_All.pipe_right uu____18169
              (fun ed ->
                 let uu____18177 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____18177 u a_tm)
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
              let uu____18212 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u] in
              match uu____18212 with
              | (uu____18217, sig_tm) ->
                  let fail t =
                    let uu____18225 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t in
                    FStar_Errors.raise_error uu____18225 r in
                  let uu____18230 =
                    let uu____18231 = FStar_Syntax_Subst.compress sig_tm in
                    uu____18231.FStar_Syntax_Syntax.n in
                  (match uu____18230 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs, uu____18235) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs in
                       (match bs1 with
                        | (a', uu____18258)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____18280 -> fail sig_tm)
                   | uu____18281 -> fail sig_tm)
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
          (let uu____18311 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects") in
           if uu____18311
           then
             let uu____18312 = FStar_Syntax_Print.comp_to_string c in
             let uu____18313 = FStar_Syntax_Print.lid_to_string tgt in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____18312 uu____18313
           else ());
          (let r = FStar_TypeChecker_Env.get_range env in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c in
           let lift_name =
             let uu____18318 =
               FStar_Ident.string_of_lid ct.FStar_Syntax_Syntax.effect_name in
             let uu____18319 = FStar_Ident.string_of_lid tgt in
             FStar_Util.format2 "%s ~> %s" uu____18318 uu____18319 in
           let uu____18320 =
             let uu____18331 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs in
             let uu____18332 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst) in
             (uu____18331, (ct.FStar_Syntax_Syntax.result_typ), uu____18332) in
           match uu____18320 with
           | (u, a, c_is) ->
               let uu____18380 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u] in
               (match uu____18380 with
                | (uu____18389, lift_t) ->
                    let lift_t_shape_error s =
                      let uu____18397 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name in
                      let uu____18398 = FStar_Ident.string_of_lid tgt in
                      let uu____18399 =
                        FStar_Syntax_Print.term_to_string lift_t in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____18397 uu____18398 s uu____18399 in
                    let uu____18400 =
                      let uu____18433 =
                        let uu____18434 = FStar_Syntax_Subst.compress lift_t in
                        uu____18434.FStar_Syntax_Syntax.n in
                      match uu____18433 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs, c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____18497 =
                            FStar_Syntax_Subst.open_comp bs c1 in
                          (match uu____18497 with
                           | (a_b::bs1, c2) ->
                               let uu____18557 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one)) in
                               (a_b, uu____18557, c2))
                      | uu____18644 ->
                          let uu____18645 =
                            let uu____18650 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders" in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____18650) in
                          FStar_Errors.raise_error uu____18645 r in
                    (match uu____18400 with
                     | (a_b, (rest_bs, f_b::[]), lift_c) ->
                         let uu____18765 =
                           let uu____18772 =
                             let uu____18773 =
                               let uu____18774 =
                                 let uu____18781 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst in
                                 (uu____18781, a) in
                               FStar_Syntax_Syntax.NT uu____18774 in
                             [uu____18773] in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____18772
                             (fun b ->
                                let uu____18798 =
                                  FStar_Syntax_Print.binder_to_string b in
                                let uu____18799 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name in
                                let uu____18800 =
                                  FStar_Ident.string_of_lid tgt in
                                let uu____18801 =
                                  FStar_Range.string_of_range r in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____18798 uu____18799 uu____18800
                                  uu____18801) r in
                         (match uu____18765 with
                          | (rest_bs_uvars, g) ->
                              ((let uu____18813 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects") in
                                if uu____18813
                                then
                                  let uu____18814 =
                                    FStar_List.fold_left
                                      (fun s ->
                                         fun u1 ->
                                           let uu____18820 =
                                             let uu____18821 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1 in
                                             Prims.op_Hat ";;;;" uu____18821 in
                                           Prims.op_Hat s uu____18820) ""
                                      rest_bs_uvars in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____18814
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b ->
                                       fun t ->
                                         let uu____18847 =
                                           let uu____18854 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst in
                                           (uu____18854, t) in
                                         FStar_Syntax_Syntax.NT uu____18847)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars) in
                                let guard_f =
                                  let f_sort =
                                    let uu____18873 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs) in
                                    FStar_All.pipe_right uu____18873
                                      FStar_Syntax_Subst.compress in
                                  let f_sort_is =
                                    let uu____18879 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name in
                                    effect_args_from_repr f_sort uu____18879
                                      r in
                                  FStar_List.fold_left2
                                    (fun g1 ->
                                       fun i1 ->
                                         fun i2 ->
                                           let uu____18887 =
                                             FStar_TypeChecker_Rel.layered_effect_teq
                                               env i1 i2
                                               (FStar_Pervasives_Native.Some
                                                  lift_name) in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____18887)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is in
                                let lift_ct =
                                  let uu____18889 =
                                    FStar_All.pipe_right lift_c
                                      (FStar_Syntax_Subst.subst_comp substs) in
                                  FStar_All.pipe_right uu____18889
                                    FStar_Syntax_Util.comp_to_comp_typ in
                                let is =
                                  let uu____18893 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____18893 r in
                                let fml =
                                  let uu____18897 =
                                    let uu____18902 =
                                      FStar_List.hd
                                        lift_ct.FStar_Syntax_Syntax.comp_univs in
                                    let uu____18903 =
                                      let uu____18904 =
                                        FStar_List.hd
                                          lift_ct.FStar_Syntax_Syntax.effect_args in
                                      FStar_Pervasives_Native.fst uu____18904 in
                                    (uu____18902, uu____18903) in
                                  match uu____18897 with
                                  | (u1, wp) ->
                                      FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                        env u1
                                        lift_ct.FStar_Syntax_Syntax.result_typ
                                        wp FStar_Range.dummyRange in
                                (let uu____18930 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects"))
                                     &&
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme) in
                                 if uu____18930
                                 then
                                   let uu____18931 =
                                     FStar_Syntax_Print.term_to_string fml in
                                   FStar_Util.print1 "Guard for lift is: %s"
                                     uu____18931
                                 else ());
                                (let c1 =
                                   let uu____18934 =
                                     let uu____18935 =
                                       FStar_All.pipe_right is
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.as_arg) in
                                     {
                                       FStar_Syntax_Syntax.comp_univs =
                                         (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                       FStar_Syntax_Syntax.effect_name = tgt;
                                       FStar_Syntax_Syntax.result_typ = a;
                                       FStar_Syntax_Syntax.effect_args =
                                         uu____18935;
                                       FStar_Syntax_Syntax.flags = []
                                     } in
                                   FStar_Syntax_Syntax.mk_Comp uu____18934 in
                                 (let uu____18959 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects") in
                                  if uu____18959
                                  then
                                    let uu____18960 =
                                      FStar_Syntax_Print.comp_to_string c1 in
                                    FStar_Util.print1 "} Lifted comp: %s\n"
                                      uu____18960
                                  else ());
                                 (let uu____18962 =
                                    let uu____18963 =
                                      FStar_TypeChecker_Env.conj_guard g
                                        guard_f in
                                    let uu____18964 =
                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                        (FStar_TypeChecker_Common.NonTrivial
                                           fml) in
                                    FStar_TypeChecker_Env.conj_guard
                                      uu____18963 uu____18964 in
                                  (c1, uu____18962)))))))))
let lift_tf_layered_effect_term :
  'uuuuuu18977 .
    'uuuuuu18977 ->
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
              let uu____19006 =
                let uu____19011 =
                  FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift
                    FStar_Util.must in
                FStar_All.pipe_right uu____19011
                  (fun ts -> FStar_TypeChecker_Env.inst_tscheme_with ts [u]) in
              FStar_All.pipe_right uu____19006 FStar_Pervasives_Native.snd in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must in
              let uu____19054 =
                let uu____19055 =
                  let uu____19058 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd in
                  FStar_All.pipe_right uu____19058
                    FStar_Syntax_Subst.compress in
                uu____19055.FStar_Syntax_Syntax.n in
              match uu____19054 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____19081::bs, uu____19083)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____19122 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one)) in
                  FStar_All.pipe_right uu____19122
                    FStar_Pervasives_Native.fst
              | uu____19227 ->
                  let uu____19228 =
                    let uu____19233 =
                      let uu____19234 =
                        FStar_Syntax_Print.tscheme_to_string lift_t in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____19234 in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____19233) in
                  FStar_Errors.raise_error uu____19228
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos in
            let args =
              let uu____19258 = FStar_Syntax_Syntax.as_arg a in
              let uu____19267 =
                let uu____19278 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____19314 ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const)) in
                let uu____19321 =
                  let uu____19332 = FStar_Syntax_Syntax.as_arg e in
                  [uu____19332] in
                FStar_List.append uu____19278 uu____19321 in
              uu____19258 :: uu____19267 in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              e.FStar_Syntax_Syntax.pos
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env ->
    fun datacon ->
      fun index ->
        let uu____19400 = FStar_TypeChecker_Env.lookup_datacon env datacon in
        match uu____19400 with
        | (uu____19405, t) ->
            let err n =
              let uu____19413 =
                let uu____19418 =
                  let uu____19419 = FStar_Ident.string_of_lid datacon in
                  let uu____19420 = FStar_Util.string_of_int n in
                  let uu____19421 = FStar_Util.string_of_int index in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____19419 uu____19420 uu____19421 in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____19418) in
              let uu____19422 = FStar_TypeChecker_Env.get_range env in
              FStar_Errors.raise_error uu____19413 uu____19422 in
            let uu____19423 =
              let uu____19424 = FStar_Syntax_Subst.compress t in
              uu____19424.FStar_Syntax_Syntax.n in
            (match uu____19423 with
             | FStar_Syntax_Syntax.Tm_arrow (bs, uu____19428) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____19483 ->
                           match uu____19483 with
                           | (uu____19490, q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true)) ->
                                    false
                                | uu____19496 -> true))) in
                 if (FStar_List.length bs1) <= index
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index in
                    FStar_Syntax_Util.mk_field_projector_name datacon
                      (FStar_Pervasives_Native.fst b) index)
             | uu____19527 -> err Prims.int_zero)
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env ->
    fun sub ->
      let uu____19538 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub.FStar_Syntax_Syntax.target) in
      if uu____19538
      then
        let uu____19539 =
          let uu____19552 =
            FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must in
          lift_tf_layered_effect sub.FStar_Syntax_Syntax.target uu____19552 in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____19539;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c in
           let uu____19586 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs in
           match uu____19586 with
           | (uu____19595, lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args in
               let uu____19614 =
                 let uu____19615 =
                   let uu___2526_19616 = ct in
                   let uu____19617 =
                     let uu____19628 =
                       let uu____19637 =
                         let uu____19638 =
                           let uu____19639 =
                             let uu____19656 =
                               let uu____19667 =
                                 FStar_Syntax_Syntax.as_arg
                                   ct.FStar_Syntax_Syntax.result_typ in
                               [uu____19667; wp] in
                             (lift_t, uu____19656) in
                           FStar_Syntax_Syntax.Tm_app uu____19639 in
                         FStar_Syntax_Syntax.mk uu____19638
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos in
                       FStar_All.pipe_right uu____19637
                         FStar_Syntax_Syntax.as_arg in
                     [uu____19628] in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2526_19616.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2526_19616.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____19617;
                     FStar_Syntax_Syntax.flags =
                       (uu___2526_19616.FStar_Syntax_Syntax.flags)
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____19615 in
               (uu____19614, FStar_TypeChecker_Common.trivial_guard) in
         let mk_mlift_term ts u r e =
           let uu____19767 = FStar_TypeChecker_Env.inst_tscheme_with ts [u] in
           match uu____19767 with
           | (uu____19774, lift_t) ->
               let uu____19776 =
                 let uu____19777 =
                   let uu____19794 =
                     let uu____19805 = FStar_Syntax_Syntax.as_arg r in
                     let uu____19814 =
                       let uu____19825 =
                         FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun in
                       let uu____19834 =
                         let uu____19845 = FStar_Syntax_Syntax.as_arg e in
                         [uu____19845] in
                       uu____19825 :: uu____19834 in
                     uu____19805 :: uu____19814 in
                   (lift_t, uu____19794) in
                 FStar_Syntax_Syntax.Tm_app uu____19777 in
               FStar_Syntax_Syntax.mk uu____19776 e.FStar_Syntax_Syntax.pos in
         let uu____19898 =
           let uu____19911 =
             FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must in
           FStar_All.pipe_right uu____19911 mk_mlift_wp in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____19898;
           FStar_TypeChecker_Env.mlift_term =
             (match sub.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____19947 ->
                        fun uu____19948 -> fun e -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env ->
    fun sub ->
      let uu____19970 = get_mlift_for_subeff env sub in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub.FStar_Syntax_Syntax.source sub.FStar_Syntax_Syntax.target
        uu____19970
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