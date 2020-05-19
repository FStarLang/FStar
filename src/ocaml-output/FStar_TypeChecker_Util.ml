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
              let ret_wp =
                FStar_All.pipe_right ed
                  FStar_Syntax_Util.get_return_vc_combinator in
              let wp =
                let uu____1368 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_a] env ed
                    ret_wp in
                let uu____1369 =
                  let uu____1370 = FStar_Syntax_Syntax.as_arg a in
                  let uu____1379 =
                    let uu____1390 = FStar_Syntax_Syntax.as_arg e in
                    [uu____1390] in
                  uu____1370 :: uu____1379 in
                FStar_Syntax_Syntax.mk_Tm_app uu____1368 uu____1369 r in
              mk_comp ed u_a a wp [FStar_Syntax_Syntax.RETURN]
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
              (let uu____1463 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "LayeredEffects") in
               if uu____1463
               then
                 let uu____1468 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                 let uu____1470 = FStar_Syntax_Print.univ_to_string u_a in
                 let uu____1472 = FStar_Syntax_Print.term_to_string a in
                 let uu____1474 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print4
                   "Computing %s.return for u_a:%s, a:%s, and e:%s{\n"
                   uu____1468 uu____1470 uu____1472 uu____1474
               else ());
              (let uu____1479 =
                 let uu____1484 =
                   FStar_All.pipe_right ed
                     FStar_Syntax_Util.get_return_vc_combinator in
                 FStar_TypeChecker_Env.inst_tscheme_with uu____1484 [u_a] in
               match uu____1479 with
               | (uu____1489, return_t) ->
                   let return_t_shape_error s =
                     let uu____1504 =
                       let uu____1506 =
                         FStar_Ident.string_of_lid
                           ed.FStar_Syntax_Syntax.mname in
                       let uu____1508 =
                         FStar_Syntax_Print.term_to_string return_t in
                       FStar_Util.format3
                         "%s.return %s does not have proper shape (reason:%s)"
                         uu____1506 uu____1508 s in
                     (FStar_Errors.Fatal_UnexpectedEffect, uu____1504) in
                   let uu____1512 =
                     let uu____1541 =
                       let uu____1542 = FStar_Syntax_Subst.compress return_t in
                       uu____1542.FStar_Syntax_Syntax.n in
                     match uu____1541 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                         (FStar_List.length bs) >= (Prims.of_int (2)) ->
                         let uu____1602 = FStar_Syntax_Subst.open_comp bs c in
                         (match uu____1602 with
                          | (a_b::x_b::bs1, c1) ->
                              let uu____1671 =
                                FStar_Syntax_Util.comp_to_comp_typ c1 in
                              (a_b, x_b, bs1, uu____1671))
                     | uu____1692 ->
                         let uu____1693 =
                           return_t_shape_error
                             "Either not an arrow or not enough binders" in
                         FStar_Errors.raise_error uu____1693 r in
                   (match uu____1512 with
                    | (a_b, x_b, rest_bs, return_ct) ->
                        let uu____1776 =
                          let uu____1783 =
                            let uu____1784 =
                              let uu____1785 =
                                let uu____1792 =
                                  FStar_All.pipe_right a_b
                                    FStar_Pervasives_Native.fst in
                                (uu____1792, a) in
                              FStar_Syntax_Syntax.NT uu____1785 in
                            let uu____1803 =
                              let uu____1806 =
                                let uu____1807 =
                                  let uu____1814 =
                                    FStar_All.pipe_right x_b
                                      FStar_Pervasives_Native.fst in
                                  (uu____1814, e) in
                                FStar_Syntax_Syntax.NT uu____1807 in
                              [uu____1806] in
                            uu____1784 :: uu____1803 in
                          FStar_TypeChecker_Env.uvars_for_binders env rest_bs
                            uu____1783
                            (fun b ->
                               let uu____1830 =
                                 FStar_Syntax_Print.binder_to_string b in
                               let uu____1832 =
                                 let uu____1834 =
                                   FStar_Ident.string_of_lid
                                     ed.FStar_Syntax_Syntax.mname in
                                 FStar_Util.format1 "%s.return" uu____1834 in
                               let uu____1837 = FStar_Range.string_of_range r in
                               FStar_Util.format3
                                 "implicit var for binder %s of %s at %s"
                                 uu____1830 uu____1832 uu____1837) r in
                        (match uu____1776 with
                         | (rest_bs_uvars, g_uvars) ->
                             let subst =
                               FStar_List.map2
                                 (fun b ->
                                    fun t ->
                                      let uu____1874 =
                                        let uu____1881 =
                                          FStar_All.pipe_right b
                                            FStar_Pervasives_Native.fst in
                                        (uu____1881, t) in
                                      FStar_Syntax_Syntax.NT uu____1874) (a_b
                                 :: x_b :: rest_bs) (a :: e :: rest_bs_uvars) in
                             let is =
                               let uu____1907 =
                                 let uu____1910 =
                                   FStar_Syntax_Subst.compress
                                     return_ct.FStar_Syntax_Syntax.result_typ in
                                 let uu____1911 =
                                   FStar_Syntax_Util.is_layered ed in
                                 effect_args_from_repr uu____1910 uu____1911
                                   r in
                               FStar_All.pipe_right uu____1907
                                 (FStar_List.map
                                    (FStar_Syntax_Subst.subst subst)) in
                             let c =
                               let uu____1918 =
                                 let uu____1919 =
                                   FStar_All.pipe_right is
                                     (FStar_List.map
                                        FStar_Syntax_Syntax.as_arg) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs = [u_a];
                                   FStar_Syntax_Syntax.effect_name =
                                     (ed.FStar_Syntax_Syntax.mname);
                                   FStar_Syntax_Syntax.result_typ = a;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____1919;
                                   FStar_Syntax_Syntax.flags = []
                                 } in
                               FStar_Syntax_Syntax.mk_Comp uu____1918 in
                             ((let uu____1943 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffects") in
                               if uu____1943
                               then
                                 let uu____1948 =
                                   FStar_Syntax_Print.comp_to_string c in
                                 FStar_Util.print1 "} c after return %s\n"
                                   uu____1948
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
              let uu____1992 =
                FStar_All.pipe_right ed FStar_Syntax_Util.is_layered in
              if uu____1992
              then mk_indexed_return env ed u_a a e r
              else
                (let uu____2002 = mk_wp_return env ed u_a a e r in
                 (uu____2002, FStar_TypeChecker_Env.trivial_guard))
let (lift_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp_typ ->
      FStar_TypeChecker_Env.mlift ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun c ->
      fun lift ->
        let uu____2027 =
          FStar_All.pipe_right
            (let uu___251_2029 = c in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___251_2029.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___251_2029.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ =
                 (uu___251_2029.FStar_Syntax_Syntax.result_typ);
               FStar_Syntax_Syntax.effect_args =
                 (uu___251_2029.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags = []
             }) FStar_Syntax_Syntax.mk_Comp in
        FStar_All.pipe_right uu____2027
          (lift.FStar_TypeChecker_Env.mlift_wp env)
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env ->
    fun l1_in ->
      fun l2_in ->
        let uu____2050 =
          let uu____2055 = FStar_TypeChecker_Env.norm_eff_name env l1_in in
          let uu____2056 = FStar_TypeChecker_Env.norm_eff_name env l2_in in
          (uu____2055, uu____2056) in
        match uu____2050 with
        | (l1, l2) ->
            let uu____2059 = FStar_TypeChecker_Env.join_opt env l1 l2 in
            (match uu____2059 with
             | FStar_Pervasives_Native.Some (m, uu____2069, uu____2070) -> m
             | FStar_Pervasives_Native.None ->
                 let uu____2083 =
                   FStar_TypeChecker_Env.exists_polymonadic_bind env l1 l2 in
                 (match uu____2083 with
                  | FStar_Pervasives_Native.Some (m, uu____2097) -> m
                  | FStar_Pervasives_Native.None ->
                      let uu____2130 =
                        let uu____2136 =
                          let uu____2138 =
                            FStar_Syntax_Print.lid_to_string l1_in in
                          let uu____2140 =
                            FStar_Syntax_Print.lid_to_string l2_in in
                          FStar_Util.format2
                            "Effects %s and %s cannot be composed" uu____2138
                            uu____2140 in
                        (FStar_Errors.Fatal_EffectsCannotBeComposed,
                          uu____2136) in
                      FStar_Errors.raise_error uu____2130
                        env.FStar_TypeChecker_Env.range))
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env ->
    fun c1 ->
      fun c2 ->
        let uu____2160 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2) in
        if uu____2160
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
            let uu____2219 =
              FStar_TypeChecker_Env.join_opt env
                c11.FStar_Syntax_Syntax.effect_name
                c21.FStar_Syntax_Syntax.effect_name in
            match uu____2219 with
            | FStar_Pervasives_Native.Some (m, lift1, lift2) ->
                let uu____2247 = lift_comp env c11 lift1 in
                (match uu____2247 with
                 | (c12, g1) ->
                     let uu____2264 =
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
                          let uu____2303 = lift_comp env_x c21 lift2 in
                          match uu____2303 with
                          | (c22, g2) ->
                              let uu____2314 =
                                FStar_TypeChecker_Env.close_guard env 
                                  [x_a] g2 in
                              (c22, uu____2314)) in
                     (match uu____2264 with
                      | (c22, g2) -> (m, c12, c22, g1, g2)))
            | FStar_Pervasives_Native.None ->
                let rng = env.FStar_TypeChecker_Env.range in
                let err uu____2361 =
                  let uu____2362 =
                    let uu____2368 =
                      let uu____2370 =
                        FStar_Syntax_Print.lid_to_string
                          c11.FStar_Syntax_Syntax.effect_name in
                      let uu____2372 =
                        FStar_Syntax_Print.lid_to_string
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____2370
                        uu____2372 in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____2368) in
                  FStar_Errors.raise_error uu____2362 rng in
                ((let uu____2387 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "LayeredEffects") in
                  if uu____2387
                  then
                    let uu____2392 =
                      let uu____2394 =
                        FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp in
                      FStar_All.pipe_right uu____2394
                        FStar_Syntax_Print.comp_to_string in
                    let uu____2396 =
                      let uu____2398 =
                        FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp in
                      FStar_All.pipe_right uu____2398
                        FStar_Syntax_Print.comp_to_string in
                    let uu____2400 = FStar_Util.string_of_bool for_bind in
                    FStar_Util.print3
                      "Lifting comps %s and %s with for_bind %s{\n"
                      uu____2392 uu____2396 uu____2400
                  else ());
                 if for_bind
                 then err ()
                 else
                   (let bind_with_return ct ret_eff f_bind =
                      let x_bv =
                        FStar_Syntax_Syntax.gen_bv "x"
                          FStar_Pervasives_Native.None
                          ct.FStar_Syntax_Syntax.result_typ in
                      let uu____2456 =
                        let uu____2461 =
                          FStar_TypeChecker_Env.push_bv env x_bv in
                        let uu____2462 =
                          FStar_TypeChecker_Env.get_effect_decl env ret_eff in
                        let uu____2463 =
                          FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs in
                        let uu____2464 = FStar_Syntax_Syntax.bv_to_name x_bv in
                        mk_return uu____2461 uu____2462 uu____2463
                          ct.FStar_Syntax_Syntax.result_typ uu____2464 rng in
                      match uu____2456 with
                      | (c_ret, g_ret) ->
                          let uu____2471 =
                            let uu____2476 =
                              FStar_Syntax_Util.comp_to_comp_typ c_ret in
                            f_bind env ct (FStar_Pervasives_Native.Some x_bv)
                              uu____2476 [] rng in
                          (match uu____2471 with
                           | (c, g_bind) ->
                               let uu____2483 =
                                 FStar_TypeChecker_Env.conj_guard g_ret
                                   g_bind in
                               (c, uu____2483)) in
                    let try_lift c12 c22 =
                      let p_bind_opt =
                        FStar_TypeChecker_Env.exists_polymonadic_bind env
                          c12.FStar_Syntax_Syntax.effect_name
                          c22.FStar_Syntax_Syntax.effect_name in
                      let uu____2528 =
                        FStar_All.pipe_right p_bind_opt FStar_Util.is_some in
                      if uu____2528
                      then
                        let uu____2564 =
                          FStar_All.pipe_right p_bind_opt FStar_Util.must in
                        match uu____2564 with
                        | (p, f_bind) ->
                            let uu____2631 =
                              FStar_Ident.lid_equals p
                                c22.FStar_Syntax_Syntax.effect_name in
                            (if uu____2631
                             then
                               let uu____2644 = bind_with_return c12 p f_bind in
                               match uu____2644 with
                               | (c13, g) ->
                                   let uu____2661 =
                                     let uu____2670 =
                                       FStar_Syntax_Syntax.mk_Comp c22 in
                                     ((c22.FStar_Syntax_Syntax.effect_name),
                                       c13, uu____2670, g) in
                                   FStar_Pervasives_Native.Some uu____2661
                             else FStar_Pervasives_Native.None)
                      else FStar_Pervasives_Native.None in
                    let uu____2699 =
                      let uu____2710 = try_lift c11 c21 in
                      match uu____2710 with
                      | FStar_Pervasives_Native.Some (p, c12, c22, g) ->
                          (p, c12, c22, g,
                            FStar_TypeChecker_Env.trivial_guard)
                      | FStar_Pervasives_Native.None ->
                          let uu____2751 = try_lift c21 c11 in
                          (match uu____2751 with
                           | FStar_Pervasives_Native.Some (p, c22, c12, g) ->
                               (p, c12, c22,
                                 FStar_TypeChecker_Env.trivial_guard, g)
                           | FStar_Pervasives_Native.None -> err ()) in
                    match uu____2699 with
                    | (p, c12, c22, g1, g2) ->
                        ((let uu____2808 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "LayeredEffects") in
                          if uu____2808
                          then
                            let uu____2813 = FStar_Ident.string_of_lid p in
                            let uu____2815 =
                              FStar_Syntax_Print.comp_to_string c12 in
                            let uu____2817 =
                              FStar_Syntax_Print.comp_to_string c22 in
                            FStar_Util.print3
                              "} Returning p %s, c1 %s, and c2 %s\n"
                              uu____2813 uu____2815 uu____2817
                          else ());
                         (p, c12, c22, g1, g2))))
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
            let uu____2870 = lift_comps_sep_guards env c1 c2 b for_bind in
            match uu____2870 with
            | (l, c11, c21, g1, g2) ->
                let uu____2894 = FStar_TypeChecker_Env.conj_guard g1 g2 in
                (l, c11, c21, uu____2894)
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
          let uu____2950 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid in
          if uu____2950
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____2962 =
      let uu____2963 = FStar_Syntax_Subst.compress t in
      uu____2963.FStar_Syntax_Syntax.n in
    match uu____2962 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2967 -> true
    | uu____2983 -> false
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
              let uu____3053 =
                let uu____3055 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____3055 in
              if uu____3053
              then f
              else (let uu____3062 = reason1 () in label uu____3062 r f)
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
            let uu___396_3083 = g in
            let uu____3084 =
              let uu____3085 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____3085 in
            {
              FStar_TypeChecker_Common.guard_f = uu____3084;
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___396_3083.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___396_3083.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___396_3083.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___396_3083.FStar_TypeChecker_Common.implicits)
            }
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun bvs ->
      fun c ->
        let uu____3106 = FStar_Syntax_Util.is_ml_comp c in
        if uu____3106
        then c
        else
          (let uu____3111 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____3111
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close =
                  let uu____3153 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator in
                  FStar_All.pipe_right uu____3153 FStar_Util.must in
                FStar_List.fold_right
                  (fun x ->
                     fun wp ->
                       let bs =
                         let uu____3182 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____3182] in
                       let us =
                         let uu____3204 =
                           let uu____3207 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____3207] in
                         u_res :: uu____3204 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu____3213 =
                         FStar_TypeChecker_Env.inst_effect_fun_with us env md
                           close in
                       let uu____3214 =
                         let uu____3215 = FStar_Syntax_Syntax.as_arg res_t in
                         let uu____3224 =
                           let uu____3235 =
                             FStar_Syntax_Syntax.as_arg
                               x.FStar_Syntax_Syntax.sort in
                           let uu____3244 =
                             let uu____3255 = FStar_Syntax_Syntax.as_arg wp1 in
                             [uu____3255] in
                           uu____3235 :: uu____3244 in
                         uu____3215 :: uu____3224 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____3213 uu____3214
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____3297 = destruct_wp_comp c1 in
              match uu____3297 with
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
                let uu____3337 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs) in
                FStar_All.pipe_right uu____3337
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
                  let uu____3387 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs) in
                  FStar_All.pipe_right uu____3387
                    (close_guard_implicits env false bs)))
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_3400 ->
            match uu___0_3400 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> true
            | uu____3403 -> false))
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env ->
    fun eopt ->
      fun lc ->
        let lc_is_unit_or_effectful =
          let uu____3428 =
            let uu____3431 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp in
            FStar_All.pipe_right uu____3431 FStar_Pervasives_Native.snd in
          FStar_All.pipe_right uu____3428
            (fun c ->
               (let uu____3455 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c in
                Prims.op_Negation uu____3455) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____3459 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c in
                     Prims.op_Negation uu____3459))) in
        match eopt with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____3470 = FStar_Syntax_Util.head_and_args' e in
                match uu____3470 with
                | (head, uu____3487) ->
                    let uu____3508 =
                      let uu____3509 = FStar_Syntax_Util.un_uinst head in
                      uu____3509.FStar_Syntax_Syntax.n in
                    (match uu____3508 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____3514 =
                           let uu____3516 = FStar_Syntax_Syntax.lid_of_fv fv in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____3516 in
                         Prims.op_Negation uu____3514
                     | uu____3517 -> true)))
              &&
              (let uu____3520 = should_not_inline_lc lc in
               Prims.op_Negation uu____3520)
let (return_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun u_t_opt ->
      fun t ->
        fun v ->
          let c =
            let uu____3548 =
              let uu____3550 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid in
              FStar_All.pipe_left Prims.op_Negation uu____3550 in
            if uu____3548
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____3557 = FStar_Syntax_Util.is_unit t in
               if uu____3557
               then
                 FStar_Syntax_Syntax.mk_Total' t
                   (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.U_zero)
               else
                 (let m =
                    FStar_TypeChecker_Env.get_effect_decl env
                      FStar_Parser_Const.effect_PURE_lid in
                  let u_t =
                    match u_t_opt with
                    | FStar_Pervasives_Native.None ->
                        env.FStar_TypeChecker_Env.universe_of env t
                    | FStar_Pervasives_Native.Some u_t -> u_t in
                  let wp =
                    let uu____3566 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____3566
                    then FStar_Syntax_Syntax.tun
                    else
                      (let ret_wp =
                         FStar_All.pipe_right m
                           FStar_Syntax_Util.get_return_vc_combinator in
                       let uu____3572 =
                         let uu____3573 =
                           FStar_TypeChecker_Env.inst_effect_fun_with 
                             [u_t] env m ret_wp in
                         let uu____3574 =
                           let uu____3575 = FStar_Syntax_Syntax.as_arg t in
                           let uu____3584 =
                             let uu____3595 = FStar_Syntax_Syntax.as_arg v in
                             [uu____3595] in
                           uu____3575 :: uu____3584 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3573 uu____3574
                           v.FStar_Syntax_Syntax.pos in
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Env.Beta;
                         FStar_TypeChecker_Env.NoFullNorm] env uu____3572) in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN])) in
          (let uu____3629 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return") in
           if uu____3629
           then
             let uu____3634 =
               FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos in
             let uu____3636 = FStar_Syntax_Print.term_to_string v in
             let uu____3638 =
               FStar_TypeChecker_Normalize.comp_to_string env c in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____3634 uu____3636 uu____3638
           else ());
          c
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
                      (let uu____3711 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LayeredEffects") in
                       if uu____3711
                       then
                         let uu____3716 =
                           let uu____3718 = FStar_Syntax_Syntax.mk_Comp ct1 in
                           FStar_Syntax_Print.comp_to_string uu____3718 in
                         let uu____3719 =
                           let uu____3721 = FStar_Syntax_Syntax.mk_Comp ct2 in
                           FStar_Syntax_Print.comp_to_string uu____3721 in
                         FStar_Util.print2 "Binding c1:%s and c2:%s {\n"
                           uu____3716 uu____3719
                       else ());
                      (let uu____3726 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "ResolveImplicitsHook") in
                       if uu____3726
                       then
                         let uu____3731 =
                           let uu____3733 =
                             FStar_TypeChecker_Env.get_range env in
                           FStar_Range.string_of_range uu____3733 in
                         let uu____3734 =
                           FStar_Syntax_Print.tscheme_to_string bind_t in
                         FStar_Util.print2
                           "///////////////////////////////Bind at %s/////////////////////\nwith bind_t = %s\n"
                           uu____3731 uu____3734
                       else ());
                      (let uu____3739 =
                         let uu____3746 =
                           FStar_TypeChecker_Env.get_effect_decl env m in
                         let uu____3747 =
                           FStar_TypeChecker_Env.get_effect_decl env n in
                         let uu____3748 =
                           FStar_TypeChecker_Env.get_effect_decl env p in
                         (uu____3746, uu____3747, uu____3748) in
                       match uu____3739 with
                       | (m_ed, n_ed, p_ed) ->
                           let uu____3756 =
                             let uu____3769 =
                               FStar_List.hd
                                 ct1.FStar_Syntax_Syntax.comp_univs in
                             let uu____3770 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 ct1.FStar_Syntax_Syntax.effect_args in
                             (uu____3769,
                               (ct1.FStar_Syntax_Syntax.result_typ),
                               uu____3770) in
                           (match uu____3756 with
                            | (u1, t1, is1) ->
                                let uu____3814 =
                                  let uu____3827 =
                                    FStar_List.hd
                                      ct2.FStar_Syntax_Syntax.comp_univs in
                                  let uu____3828 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst
                                      ct2.FStar_Syntax_Syntax.effect_args in
                                  (uu____3827,
                                    (ct2.FStar_Syntax_Syntax.result_typ),
                                    uu____3828) in
                                (match uu____3814 with
                                 | (u2, t2, is2) ->
                                     let uu____3872 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         bind_t [u1; u2] in
                                     (match uu____3872 with
                                      | (uu____3881, bind_t1) ->
                                          let bind_t_shape_error s =
                                            let uu____3896 =
                                              let uu____3898 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t1 in
                                              FStar_Util.format2
                                                "bind %s does not have proper shape (reason:%s)"
                                                uu____3898 s in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu____3896) in
                                          let uu____3902 =
                                            let uu____3947 =
                                              let uu____3948 =
                                                FStar_Syntax_Subst.compress
                                                  bind_t1 in
                                              uu____3948.FStar_Syntax_Syntax.n in
                                            match uu____3947 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs, c) when
                                                (FStar_List.length bs) >=
                                                  (Prims.of_int (4))
                                                ->
                                                let uu____4024 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs c in
                                                (match uu____4024 with
                                                 | (a_b::b_b::bs1, c1) ->
                                                     let uu____4109 =
                                                       let uu____4136 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2)))
                                                           bs1 in
                                                       FStar_All.pipe_right
                                                         uu____4136
                                                         (fun uu____4221 ->
                                                            match uu____4221
                                                            with
                                                            | (l1, l2) ->
                                                                let uu____4302
                                                                  =
                                                                  FStar_List.hd
                                                                    l2 in
                                                                let uu____4315
                                                                  =
                                                                  let uu____4322
                                                                    =
                                                                    FStar_List.tl
                                                                    l2 in
                                                                  FStar_List.hd
                                                                    uu____4322 in
                                                                (l1,
                                                                  uu____4302,
                                                                  uu____4315)) in
                                                     (match uu____4109 with
                                                      | (rest_bs, f_b, g_b)
                                                          ->
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b, c1)))
                                            | uu____4482 ->
                                                let uu____4483 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders" in
                                                FStar_Errors.raise_error
                                                  uu____4483 r1 in
                                          (match uu____3902 with
                                           | (a_b, b_b, rest_bs, f_b, g_b,
                                              bind_c) ->
                                               let uu____4608 =
                                                 let uu____4615 =
                                                   let uu____4616 =
                                                     let uu____4617 =
                                                       let uu____4624 =
                                                         FStar_All.pipe_right
                                                           a_b
                                                           FStar_Pervasives_Native.fst in
                                                       (uu____4624, t1) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____4617 in
                                                   let uu____4635 =
                                                     let uu____4638 =
                                                       let uu____4639 =
                                                         let uu____4646 =
                                                           FStar_All.pipe_right
                                                             b_b
                                                             FStar_Pervasives_Native.fst in
                                                         (uu____4646, t2) in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____4639 in
                                                     [uu____4638] in
                                                   uu____4616 :: uu____4635 in
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs uu____4615
                                                   (fun b1 ->
                                                      let uu____4662 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1 in
                                                      let uu____4664 =
                                                        let uu____4666 =
                                                          FStar_Ident.string_of_lid
                                                            m in
                                                        let uu____4668 =
                                                          FStar_Ident.string_of_lid
                                                            n in
                                                        let uu____4670 =
                                                          FStar_Ident.string_of_lid
                                                            p in
                                                        FStar_Util.format3
                                                          "(%s, %s) |> %s"
                                                          uu____4666
                                                          uu____4668
                                                          uu____4670 in
                                                      let uu____4673 =
                                                        FStar_Range.string_of_range
                                                          r1 in
                                                      FStar_Util.format3
                                                        "implicit var for binder %s of %s at %s"
                                                        uu____4662 uu____4664
                                                        uu____4673) r1 in
                                               (match uu____4608 with
                                                | (rest_bs_uvars, g_uvars) ->
                                                    ((let uu____4687 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "ResolveImplicitsHook") in
                                                      if uu____4687
                                                      then
                                                        FStar_All.pipe_right
                                                          rest_bs_uvars
                                                          (FStar_List.iter
                                                             (fun t ->
                                                                let uu____4701
                                                                  =
                                                                  let uu____4702
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    t in
                                                                  uu____4702.FStar_Syntax_Syntax.n in
                                                                match uu____4701
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (u,
                                                                    uu____4706)
                                                                    ->
                                                                    let uu____4723
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t in
                                                                    let uu____4725
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
                                                                    uu____4731
                                                                    ->
                                                                    "<no attr>" in
                                                                    FStar_Util.print2
                                                                    "Generated uvar %s with attribute %s\n"
                                                                    uu____4723
                                                                    uu____4725))
                                                      else ());
                                                     (let subst =
                                                        FStar_List.map2
                                                          (fun b1 ->
                                                             fun t ->
                                                               let uu____4762
                                                                 =
                                                                 let uu____4769
                                                                   =
                                                                   FStar_All.pipe_right
                                                                    b1
                                                                    FStar_Pervasives_Native.fst in
                                                                 (uu____4769,
                                                                   t) in
                                                               FStar_Syntax_Syntax.NT
                                                                 uu____4762)
                                                          (a_b :: b_b ::
                                                          rest_bs) (t1 :: t2
                                                          :: rest_bs_uvars) in
                                                      let f_guard =
                                                        let f_sort_is =
                                                          let uu____4798 =
                                                            let uu____4801 =
                                                              let uu____4802
                                                                =
                                                                let uu____4803
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    f_b
                                                                    FStar_Pervasives_Native.fst in
                                                                uu____4803.FStar_Syntax_Syntax.sort in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4802 in
                                                            let uu____4812 =
                                                              FStar_Syntax_Util.is_layered
                                                                m_ed in
                                                            effect_args_from_repr
                                                              uu____4801
                                                              uu____4812 r1 in
                                                          FStar_All.pipe_right
                                                            uu____4798
                                                            (FStar_List.map
                                                               (FStar_Syntax_Subst.subst
                                                                  subst)) in
                                                        FStar_List.fold_left2
                                                          (fun g ->
                                                             fun i1 ->
                                                               fun f_i1 ->
                                                                 (let uu____4837
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "ResolveImplicitsHook") in
                                                                  if
                                                                    uu____4837
                                                                  then
                                                                    let uu____4842
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    i1 in
                                                                    let uu____4844
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    f_i1 in
                                                                    FStar_Util.print2
                                                                    "Generating constraint %s = %s\n"
                                                                    uu____4842
                                                                    uu____4844
                                                                  else ());
                                                                 (let uu____4849
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env i1
                                                                    f_i1 in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____4849))
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
                                                          let uu____4868 =
                                                            let uu____4869 =
                                                              let uu____4872
                                                                =
                                                                let uu____4873
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    g_b
                                                                    FStar_Pervasives_Native.fst in
                                                                uu____4873.FStar_Syntax_Syntax.sort in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4872 in
                                                            uu____4869.FStar_Syntax_Syntax.n in
                                                          match uu____4868
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_arrow
                                                              (bs, c) ->
                                                              let uu____4906
                                                                =
                                                                FStar_Syntax_Subst.open_comp
                                                                  bs c in
                                                              (match uu____4906
                                                               with
                                                               | (bs1, c1) ->
                                                                   let bs_subst
                                                                    =
                                                                    let uu____4916
                                                                    =
                                                                    let uu____4923
                                                                    =
                                                                    let uu____4924
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1 in
                                                                    FStar_All.pipe_right
                                                                    uu____4924
                                                                    FStar_Pervasives_Native.fst in
                                                                    let uu____4945
                                                                    =
                                                                    let uu____4948
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst in
                                                                    FStar_All.pipe_right
                                                                    uu____4948
                                                                    FStar_Syntax_Syntax.bv_to_name in
                                                                    (uu____4923,
                                                                    uu____4945) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4916 in
                                                                   let c2 =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1 in
                                                                   let uu____4962
                                                                    =
                                                                    let uu____4965
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2) in
                                                                    let uu____4966
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed in
                                                                    effect_args_from_repr
                                                                    uu____4965
                                                                    uu____4966
                                                                    r1 in
                                                                   FStar_All.pipe_right
                                                                    uu____4962
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst)))
                                                          | uu____4972 ->
                                                              failwith
                                                                "imspossible: mk_indexed_bind" in
                                                        let env_g =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env [x_a] in
                                                        let uu____4989 =
                                                          FStar_List.fold_left2
                                                            (fun g ->
                                                               fun i1 ->
                                                                 fun g_i1 ->
                                                                   (let uu____5007
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "ResolveImplicitsHook") in
                                                                    if
                                                                    uu____5007
                                                                    then
                                                                    let uu____5012
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    i1 in
                                                                    let uu____5014
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    g_i1 in
                                                                    FStar_Util.print2
                                                                    "Generating constraint %s = %s\n"
                                                                    uu____5012
                                                                    uu____5014
                                                                    else ());
                                                                   (let uu____5019
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env_g i1
                                                                    g_i1 in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____5019))
                                                            FStar_TypeChecker_Env.trivial_guard
                                                            is2 g_sort_is in
                                                        FStar_All.pipe_right
                                                          uu____4989
                                                          (FStar_TypeChecker_Env.close_guard
                                                             env [x_a]) in
                                                      let bind_ct =
                                                        let uu____5033 =
                                                          FStar_All.pipe_right
                                                            bind_c
                                                            (FStar_Syntax_Subst.subst_comp
                                                               subst) in
                                                        FStar_All.pipe_right
                                                          uu____5033
                                                          FStar_Syntax_Util.comp_to_comp_typ in
                                                      let fml =
                                                        let uu____5035 =
                                                          let uu____5040 =
                                                            FStar_List.hd
                                                              bind_ct.FStar_Syntax_Syntax.comp_univs in
                                                          let uu____5041 =
                                                            let uu____5042 =
                                                              FStar_List.hd
                                                                bind_ct.FStar_Syntax_Syntax.effect_args in
                                                            FStar_Pervasives_Native.fst
                                                              uu____5042 in
                                                          (uu____5040,
                                                            uu____5041) in
                                                        match uu____5035 with
                                                        | (u, wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              bind_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange in
                                                      let is =
                                                        let uu____5068 =
                                                          FStar_Syntax_Subst.compress
                                                            bind_ct.FStar_Syntax_Syntax.result_typ in
                                                        let uu____5069 =
                                                          FStar_Syntax_Util.is_layered
                                                            p_ed in
                                                        effect_args_from_repr
                                                          uu____5068
                                                          uu____5069 r1 in
                                                      let c =
                                                        let uu____5072 =
                                                          let uu____5073 =
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
                                                              = uu____5073;
                                                            FStar_Syntax_Syntax.flags
                                                              = flags
                                                          } in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____5072 in
                                                      (let uu____5093 =
                                                         FStar_All.pipe_left
                                                           (FStar_TypeChecker_Env.debug
                                                              env)
                                                           (FStar_Options.Other
                                                              "LayeredEffects") in
                                                       if uu____5093
                                                       then
                                                         let uu____5098 =
                                                           FStar_Syntax_Print.comp_to_string
                                                             c in
                                                         FStar_Util.print1
                                                           "} c after bind: %s\n"
                                                           uu____5098
                                                       else ());
                                                      (let guard =
                                                         let uu____5104 =
                                                           let uu____5107 =
                                                             let uu____5110 =
                                                               let uu____5113
                                                                 =
                                                                 let uu____5116
                                                                   =
                                                                   FStar_TypeChecker_Env.guard_of_guard_formula
                                                                    (FStar_TypeChecker_Common.NonTrivial
                                                                    fml) in
                                                                 [uu____5116] in
                                                               g_guard ::
                                                                 uu____5113 in
                                                             f_guard ::
                                                               uu____5110 in
                                                           g_uvars ::
                                                             uu____5107 in
                                                         FStar_TypeChecker_Env.conj_guards
                                                           uu____5104 in
                                                       (let uu____5118 =
                                                          FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "ResolveImplicitsHook") in
                                                        if uu____5118
                                                        then
                                                          let uu____5123 =
                                                            let uu____5125 =
                                                              FStar_TypeChecker_Env.get_range
                                                                env in
                                                            FStar_Range.string_of_range
                                                              uu____5125 in
                                                          let uu____5126 =
                                                            FStar_TypeChecker_Rel.guard_to_string
                                                              env guard in
                                                          FStar_Util.print2
                                                            "///////////////////////////////EndBind at %s/////////////////////\nguard = %s\n"
                                                            uu____5123
                                                            uu____5126
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
                let uu____5175 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m in
                  let uu____5201 = FStar_TypeChecker_Env.wp_signature env m in
                  match uu____5201 with
                  | (a, kwp) ->
                      let uu____5232 = destruct_wp_comp ct1 in
                      let uu____5239 = destruct_wp_comp ct2 in
                      ((md, a, kwp), uu____5232, uu____5239) in
                match uu____5175 with
                | ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None ->
                          let uu____5292 = FStar_Syntax_Syntax.null_binder t1 in
                          [uu____5292]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____5312 = FStar_Syntax_Syntax.mk_binder x in
                          [uu____5312] in
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
                      let uu____5359 = FStar_Syntax_Syntax.as_arg r11 in
                      let uu____5368 =
                        let uu____5379 = FStar_Syntax_Syntax.as_arg t1 in
                        let uu____5388 =
                          let uu____5399 = FStar_Syntax_Syntax.as_arg t2 in
                          let uu____5408 =
                            let uu____5419 = FStar_Syntax_Syntax.as_arg wp1 in
                            let uu____5428 =
                              let uu____5439 =
                                let uu____5448 = mk_lam wp2 in
                                FStar_Syntax_Syntax.as_arg uu____5448 in
                              [uu____5439] in
                            uu____5419 :: uu____5428 in
                          uu____5399 :: uu____5408 in
                        uu____5379 :: uu____5388 in
                      uu____5359 :: uu____5368 in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator in
                    let wp =
                      let uu____5499 =
                        FStar_TypeChecker_Env.inst_effect_fun_with
                          [u_t1; u_t2] env md bind_wp in
                      FStar_Syntax_Syntax.mk_Tm_app uu____5499 wp_args
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
              let uu____5547 =
                let uu____5552 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1 in
                let uu____5553 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2 in
                (uu____5552, uu____5553) in
              match uu____5547 with
              | (ct1, ct2) ->
                  let uu____5560 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name in
                  (match uu____5560 with
                   | FStar_Pervasives_Native.Some (p, f_bind) ->
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None ->
                       let uu____5611 = lift_comps env c1 c2 b true in
                       (match uu____5611 with
                        | (m, c11, c21, g_lift) ->
                            let uu____5629 =
                              let uu____5634 =
                                FStar_Syntax_Util.comp_to_comp_typ c11 in
                              let uu____5635 =
                                FStar_Syntax_Util.comp_to_comp_typ c21 in
                              (uu____5634, uu____5635) in
                            (match uu____5629 with
                             | (ct11, ct21) ->
                                 let uu____5642 =
                                   let uu____5647 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m in
                                   if uu____5647
                                   then
                                     let bind_t =
                                       let uu____5655 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env) in
                                       FStar_All.pipe_right uu____5655
                                         FStar_Syntax_Util.get_bind_vc_combinator in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu____5658 =
                                        mk_wp_bind env m ct11 b ct21 flags r1 in
                                      (uu____5658,
                                        FStar_TypeChecker_Env.trivial_guard)) in
                                 (match uu____5642 with
                                  | (c, g_bind) ->
                                      let uu____5665 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind in
                                      (c, uu____5665)))))
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
            let uu____5701 =
              let uu____5702 =
                let uu____5713 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg in
                [uu____5713] in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____5702;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____5701 in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags ->
    let uu____5758 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_5764 ->
              match uu___1_5764 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> true
              | uu____5767 -> false)) in
    if uu____5758
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_5779 ->
              match uu___2_5779 with
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
        let uu____5807 = FStar_Syntax_Util.is_ml_comp c in
        if uu____5807
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
           let pure_assume_wp =
             let uu____5818 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None in
             FStar_Syntax_Syntax.fv_to_tm uu____5818 in
           let pure_assume_wp1 =
             let uu____5821 =
               let uu____5822 =
                 FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula in
               [uu____5822] in
             let uu____5855 = FStar_TypeChecker_Env.get_range env in
             FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____5821
               uu____5855 in
           let uu____5856 = weaken_flags ct.FStar_Syntax_Syntax.flags in
           bind_pure_wp_with env pure_assume_wp1 c uu____5856)
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env ->
    fun lc ->
      fun f ->
        let weaken uu____5884 =
          let uu____5885 = FStar_TypeChecker_Common.lcomp_comp lc in
          match uu____5885 with
          | (c, g_c) ->
              let uu____5896 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
              if uu____5896
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5910 = weaken_comp env c f1 in
                     (match uu____5910 with
                      | (c1, g_w) ->
                          let uu____5921 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w in
                          (c1, uu____5921))) in
        let uu____5922 = weaken_flags lc.FStar_TypeChecker_Common.cflags in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5922 weaken
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
                 let uu____5979 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None in
                 FStar_Syntax_Syntax.fv_to_tm uu____5979 in
               let pure_assert_wp1 =
                 let uu____5982 =
                   let uu____5983 =
                     let uu____5992 = label_opt env reason r f in
                     FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                       uu____5992 in
                   [uu____5983] in
                 FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____5982 r in
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
            let uu____6062 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0 in
            if uu____6062
            then (lc, g0)
            else
              (let flags =
                 let uu____6074 =
                   let uu____6082 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc in
                   if uu____6082
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, []) in
                 match uu____6074 with
                 | (maybe_trivial_post, flags) ->
                     let uu____6112 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_6120 ->
                               match uu___3_6120 with
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
                               | uu____6123 -> [])) in
                     FStar_List.append flags uu____6112 in
               let strengthen uu____6133 =
                 let uu____6134 = FStar_TypeChecker_Common.lcomp_comp lc in
                 match uu____6134 with
                 | (c, g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                        let uu____6153 = FStar_TypeChecker_Env.guard_form g01 in
                        match uu____6153 with
                        | FStar_TypeChecker_Common.Trivial -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____6160 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____6160
                              then
                                let uu____6164 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only in
                                let uu____6166 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____6164 uu____6166
                              else ());
                             (let uu____6171 =
                                strengthen_comp env reason c f flags in
                              match uu____6171 with
                              | (c1, g_s) ->
                                  let uu____6182 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s in
                                  (c1, uu____6182)))) in
               let uu____6183 =
                 let uu____6184 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name in
                 FStar_TypeChecker_Common.mk_lcomp uu____6184
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen in
               (uu____6183,
                 (let uu___727_6186 = g0 in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred_to_tac =
                      (uu___727_6186.FStar_TypeChecker_Common.deferred_to_tac);
                    FStar_TypeChecker_Common.deferred =
                      (uu___727_6186.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___727_6186.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___727_6186.FStar_TypeChecker_Common.implicits)
                  })))
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_6195 ->
            match uu___4_6195 with
            | FStar_Syntax_Syntax.SOMETRIVIAL -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION -> true
            | uu____6199 -> false) lc.FStar_TypeChecker_Common.cflags)
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
          let uu____6228 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax in
          if uu____6228
          then e
          else
            (let uu____6235 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____6238 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid in
                  FStar_Option.isSome uu____6238) in
             if uu____6235
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
                | uu____6308 -> false in
              if is_unit
              then
                let uu____6315 =
                  let uu____6317 =
                    let uu____6318 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name in
                    FStar_All.pipe_right uu____6318
                      (FStar_TypeChecker_Env.norm_eff_name env) in
                  FStar_All.pipe_right uu____6317
                    (FStar_TypeChecker_Env.is_layered_effect env) in
                (if uu____6315
                 then
                   let uu____6327 = FStar_Syntax_Subst.open_term_bv b phi in
                   match uu____6327 with
                   | (b1, phi1) ->
                       let phi2 =
                         FStar_Syntax_Subst.subst
                           [FStar_Syntax_Syntax.NT
                              (b1, FStar_Syntax_Syntax.unit_const)] phi1 in
                       weaken_comp env c phi2
                 else
                   (let uu____6343 = close_wp_comp env [x] c in
                    (uu____6343, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____6346 -> (c, FStar_TypeChecker_Env.trivial_guard)
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
          fun uu____6374 ->
            match uu____6374 with
            | (b, lc2) ->
                let debug f =
                  let uu____6394 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____6394 then f () else () in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                let bind_flags =
                  let uu____6407 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21) in
                  if uu____6407
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____6417 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11 in
                       if uu____6417
                       then
                         let uu____6422 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21 in
                         (if uu____6422
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____6429 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21 in
                             if uu____6429
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____6438 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21) in
                          if uu____6438
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else []) in
                     let uu____6445 = lcomp_has_trivial_postcondition lc21 in
                     if uu____6445
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags) in
                let bind_it uu____6461 =
                  let uu____6462 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ()) in
                  if uu____6462
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ in
                    let uu____6470 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ [] in
                    (uu____6470, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____6473 =
                       FStar_TypeChecker_Common.lcomp_comp lc11 in
                     match uu____6473 with
                     | (c1, g_c1) ->
                         let uu____6484 =
                           FStar_TypeChecker_Common.lcomp_comp lc21 in
                         (match uu____6484 with
                          | (c2, g_c2) ->
                              let trivial_guard =
                                let uu____6496 =
                                  match b with
                                  | FStar_Pervasives_Native.Some x ->
                                      let b1 =
                                        FStar_Syntax_Syntax.mk_binder x in
                                      let uu____6499 =
                                        FStar_Syntax_Syntax.is_null_binder b1 in
                                      if uu____6499
                                      then g_c2
                                      else
                                        FStar_TypeChecker_Env.close_guard env
                                          [b1] g_c2
                                  | FStar_Pervasives_Native.None -> g_c2 in
                                FStar_TypeChecker_Env.conj_guard g_c1
                                  uu____6496 in
                              (debug
                                 (fun uu____6525 ->
                                    let uu____6526 =
                                      FStar_Syntax_Print.comp_to_string c1 in
                                    let uu____6528 =
                                      match b with
                                      | FStar_Pervasives_Native.None ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x in
                                    let uu____6533 =
                                      FStar_Syntax_Print.comp_to_string c2 in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____6526 uu____6528 uu____6533);
                               (let aux uu____6551 =
                                  let uu____6552 =
                                    FStar_Syntax_Util.is_trivial_wp c1 in
                                  if uu____6552
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____6583
                                        ->
                                        let uu____6584 =
                                          FStar_Syntax_Util.is_ml_comp c2 in
                                        (if uu____6584
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____6616 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2) in
                                     if uu____6616
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML") in
                                let try_simplify uu____6663 =
                                  let aux_with_trivial_guard uu____6693 =
                                    let uu____6694 = aux () in
                                    match uu____6694 with
                                    | FStar_Util.Inl (c, reason) ->
                                        FStar_Util.Inl
                                          (c, trivial_guard, reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason in
                                  let uu____6752 =
                                    let uu____6754 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid in
                                    FStar_Option.isNone uu____6754 in
                                  if uu____6752
                                  then
                                    let uu____6770 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2) in
                                    (if uu____6770
                                     then
                                       FStar_Util.Inl
                                         (c2, trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____6797 =
                                          FStar_TypeChecker_Env.get_range env in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____6797))
                                  else
                                    (let uu____6814 =
                                       FStar_Syntax_Util.is_total_comp c1 in
                                     if uu____6814
                                     then
                                       let close_with_type_of_x x c =
                                         let x1 =
                                           let uu___830_6845 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___830_6845.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___830_6845.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         maybe_capture_unit_refinement env
                                           x1.FStar_Syntax_Syntax.sort x1 c in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some e,
                                          FStar_Pervasives_Native.Some x) ->
                                           let uu____6876 =
                                             let uu____6881 =
                                               FStar_All.pipe_right c2
                                                 (FStar_Syntax_Subst.subst_comp
                                                    [FStar_Syntax_Syntax.NT
                                                       (x, e)]) in
                                             FStar_All.pipe_right uu____6881
                                               (close_with_type_of_x x) in
                                           (match uu____6876 with
                                            | (c21, g_close) ->
                                                let uu____6902 =
                                                  let uu____6910 =
                                                    let uu____6911 =
                                                      let uu____6914 =
                                                        let uu____6917 =
                                                          FStar_TypeChecker_Env.map_guard
                                                            g_c2
                                                            (FStar_Syntax_Subst.subst
                                                               [FStar_Syntax_Syntax.NT
                                                                  (x, e)]) in
                                                        [uu____6917; g_close] in
                                                      g_c1 :: uu____6914 in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6911 in
                                                  (c21, uu____6910, "c1 Tot") in
                                                FStar_Util.Inl uu____6902)
                                       | (uu____6930,
                                          FStar_Pervasives_Native.Some x) ->
                                           let uu____6942 =
                                             FStar_All.pipe_right c2
                                               (close_with_type_of_x x) in
                                           (match uu____6942 with
                                            | (c21, g_close) ->
                                                let uu____6965 =
                                                  let uu____6973 =
                                                    let uu____6974 =
                                                      let uu____6977 =
                                                        let uu____6980 =
                                                          let uu____6981 =
                                                            let uu____6982 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x in
                                                            [uu____6982] in
                                                          FStar_TypeChecker_Env.close_guard
                                                            env uu____6981
                                                            g_c2 in
                                                        [uu____6980; g_close] in
                                                      g_c1 :: uu____6977 in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6974 in
                                                  (c21, uu____6973,
                                                    "c1 Tot only close") in
                                                FStar_Util.Inl uu____6965)
                                       | (uu____7011, uu____7012) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____7027 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2) in
                                        if uu____7027
                                        then
                                          let uu____7042 =
                                            let uu____7050 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2) in
                                            (uu____7050, trivial_guard,
                                              "both GTot") in
                                          FStar_Util.Inl uu____7042
                                        else aux_with_trivial_guard ())) in
                                let uu____7063 = try_simplify () in
                                match uu____7063 with
                                | FStar_Util.Inl (c, g, reason) ->
                                    (debug
                                       (fun uu____7098 ->
                                          let uu____7099 =
                                            FStar_Syntax_Print.comp_to_string
                                              c in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____7099);
                                     (c, g))
                                | FStar_Util.Inr reason ->
                                    (debug
                                       (fun uu____7115 ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 g =
                                        let uu____7146 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1 in
                                        match uu____7146 with
                                        | (c, g_bind) ->
                                            let uu____7157 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g g_bind in
                                            (c, uu____7157) in
                                      let mk_seq c11 b1 c21 =
                                        let c12 =
                                          FStar_TypeChecker_Env.unfold_effect_abbrev
                                            env c11 in
                                        let c22 =
                                          FStar_TypeChecker_Env.unfold_effect_abbrev
                                            env c21 in
                                        let uu____7184 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name in
                                        match uu____7184 with
                                        | (m, uu____7196, lift2) ->
                                            let uu____7198 =
                                              lift_comp env c22 lift2 in
                                            (match uu____7198 with
                                             | (c23, g2) ->
                                                 let uu____7209 =
                                                   destruct_wp_comp c12 in
                                                 (match uu____7209 with
                                                  | (u1, t1, wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name in
                                                      let trivial =
                                                        let uu____7225 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator in
                                                        FStar_All.pipe_right
                                                          uu____7225
                                                          FStar_Util.must in
                                                      let vc1 =
                                                        let uu____7233 =
                                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                                            [u1] env
                                                            md_pure_or_ghost
                                                            trivial in
                                                        let uu____7234 =
                                                          let uu____7235 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              t1 in
                                                          let uu____7244 =
                                                            let uu____7255 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                wp1 in
                                                            [uu____7255] in
                                                          uu____7235 ::
                                                            uu____7244 in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7233
                                                          uu____7234 r1 in
                                                      let uu____7288 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags in
                                                      (match uu____7288 with
                                                       | (c, g_s) ->
                                                           let uu____7303 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s] in
                                                           (c, uu____7303)))) in
                                      let uu____7304 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1 in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None ->
                                            let uu____7320 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t in
                                            (uu____7320, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t) in
                                      match uu____7304 with
                                      | (u_res_t1, res_t1) ->
                                          let uu____7336 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11) in
                                          if uu____7336
                                          then
                                            let e1 = FStar_Option.get e1opt in
                                            let x = FStar_Option.get b in
                                            let uu____7345 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1 in
                                            (if uu____7345
                                             then
                                               (debug
                                                  (fun uu____7359 ->
                                                     let uu____7360 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1 in
                                                     let uu____7362 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____7360 uu____7362);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2 in
                                                 let g =
                                                   let uu____7369 =
                                                     FStar_TypeChecker_Env.map_guard
                                                       g_c2
                                                       (FStar_Syntax_Subst.subst
                                                          [FStar_Syntax_Syntax.NT
                                                             (x, e1)]) in
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 uu____7369 in
                                                 mk_bind1 c1 b c21 g))
                                             else
                                               (let uu____7374 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____7377 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid in
                                                     FStar_Option.isSome
                                                       uu____7377) in
                                                if uu____7374
                                                then
                                                  let e1' =
                                                    let uu____7402 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        () in
                                                    if uu____7402
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1 in
                                                  (debug
                                                     (fun uu____7414 ->
                                                        let uu____7415 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1' in
                                                        let uu____7417 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____7415
                                                          uu____7417);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2 in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug
                                                     (fun uu____7432 ->
                                                        let uu____7433 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1 in
                                                        let uu____7435 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____7433
                                                          uu____7435);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2 in
                                                    let x_eq_e =
                                                      let uu____7442 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____7442 in
                                                    let uu____7443 =
                                                      let uu____7448 =
                                                        let uu____7449 =
                                                          let uu____7450 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x in
                                                          [uu____7450] in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____7449 in
                                                      weaken_comp uu____7448
                                                        c21 x_eq_e in
                                                    match uu____7443 with
                                                    | (c22, g_w) ->
                                                        let g =
                                                          let uu____7476 =
                                                            let uu____7477 =
                                                              let uu____7478
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x in
                                                              [uu____7478] in
                                                            let uu____7497 =
                                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                                g_c2 x_eq_e in
                                                            FStar_TypeChecker_Env.close_guard
                                                              env uu____7477
                                                              uu____7497 in
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g_c1 uu____7476 in
                                                        let uu____7498 =
                                                          mk_bind1 c1 b c22 g in
                                                        (match uu____7498
                                                         with
                                                         | (c, g_bind) ->
                                                             let uu____7509 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind in
                                                             (c, uu____7509))))))
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
      | uu____7526 -> g2
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
            (let uu____7550 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc in
             Prims.op_Negation uu____7550) in
        let flags =
          if should_return1
          then
            let uu____7558 = FStar_TypeChecker_Common.is_total_lcomp lc in
            (if uu____7558
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags in
        let refine uu____7576 =
          let uu____7577 = FStar_TypeChecker_Common.lcomp_comp lc in
          match uu____7577 with
          | (c, g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c) in
              let uu____7590 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
              if uu____7590
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e in
                let uu____7598 =
                  let uu____7600 = FStar_Syntax_Util.is_pure_comp c in
                  Prims.op_Negation uu____7600 in
                (if uu____7598
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                   let retc2 =
                     let uu___955_7609 = retc1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___955_7609.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___955_7609.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___955_7609.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     } in
                   let uu____7610 = FStar_Syntax_Syntax.mk_Comp retc2 in
                   (uu____7610, g_c)
                 else
                   (let uu____7613 =
                      FStar_Syntax_Util.comp_set_flags retc flags in
                    (uu____7613, g_c)))
              else
                (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 let t = c1.FStar_Syntax_Syntax.result_typ in
                 let c2 = FStar_Syntax_Syntax.mk_Comp c1 in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (t.FStar_Syntax_Syntax.pos)) t in
                 let xexp = FStar_Syntax_Syntax.bv_to_name x in
                 let ret =
                   let uu____7624 =
                     let uu____7625 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp in
                     FStar_Syntax_Util.comp_set_flags uu____7625
                       [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____7624 in
                 let eq = FStar_Syntax_Util.mk_eq2 u_t t xexp e in
                 let eq_ret =
                   weaken_precondition env ret
                     (FStar_TypeChecker_Common.NonTrivial eq) in
                 let uu____7628 =
                   let uu____7633 =
                     let uu____7634 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2 in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____7634
                       ((FStar_Pervasives_Native.Some x), eq_ret) in
                   FStar_TypeChecker_Common.lcomp_comp uu____7633 in
                 match uu____7628 with
                 | (bind_c, g_bind) ->
                     let uu____7643 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags in
                     let uu____7644 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind in
                     (uu____7643, uu____7644)) in
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
            fun uu____7680 ->
              match uu____7680 with
              | (x, lc2) ->
                  let lc21 =
                    let eff1 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc1.FStar_TypeChecker_Common.eff_name in
                    let eff2 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc2.FStar_TypeChecker_Common.eff_name in
                    let uu____7692 =
                      ((let uu____7696 = is_pure_or_ghost_effect env eff1 in
                        Prims.op_Negation uu____7696) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2) in
                    if uu____7692
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2 in
                  bind r env e1opt lc1 (x, lc21)
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun lid ->
      let uu____7714 =
        let uu____7715 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____7715 in
      FStar_Syntax_Syntax.fvar uu____7714 FStar_Syntax_Syntax.delta_constant
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
                  let uu____7765 =
                    let uu____7770 =
                      let uu____7771 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator in
                      FStar_All.pipe_right uu____7771 FStar_Util.must in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7770 [u_a] in
                  match uu____7765 with
                  | (uu____7782, conjunction) ->
                      let uu____7784 =
                        let uu____7793 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args in
                        let uu____7808 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args in
                        (uu____7793, uu____7808) in
                      (match uu____7784 with
                       | (is1, is2) ->
                           let conjunction_t_error s =
                             let uu____7854 =
                               let uu____7856 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____7856 s in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7854) in
                           let uu____7860 =
                             let uu____7905 =
                               let uu____7906 =
                                 FStar_Syntax_Subst.compress conjunction in
                               uu____7906.FStar_Syntax_Syntax.n in
                             match uu____7905 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs, body, uu____7955) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____7987 =
                                   FStar_Syntax_Subst.open_term bs body in
                                 (match uu____7987 with
                                  | (a_b::bs1, body1) ->
                                      let uu____8059 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1 in
                                      (match uu____8059 with
                                       | (rest_bs, f_b::g_b::p_b::[]) ->
                                           let uu____8207 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____8207)))
                             | uu____8240 ->
                                 let uu____8241 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders" in
                                 FStar_Errors.raise_error uu____8241 r in
                           (match uu____7860 with
                            | (a_b, rest_bs, f_b, g_b, p_b, body) ->
                                let uu____8366 =
                                  let uu____8373 =
                                    let uu____8374 =
                                      let uu____8375 =
                                        let uu____8382 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst in
                                        (uu____8382, a) in
                                      FStar_Syntax_Syntax.NT uu____8375 in
                                    [uu____8374] in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____8373
                                    (fun b ->
                                       let uu____8398 =
                                         FStar_Syntax_Print.binder_to_string
                                           b in
                                       let uu____8400 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname in
                                       let uu____8402 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____8398 uu____8400 uu____8402) r in
                                (match uu____8366 with
                                 | (rest_bs_uvars, g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b ->
                                            fun t ->
                                              let uu____8440 =
                                                let uu____8447 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst in
                                                (uu____8447, t) in
                                              FStar_Syntax_Syntax.NT
                                                uu____8440) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p])) in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____8486 =
                                           let uu____8487 =
                                             let uu____8490 =
                                               let uu____8491 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst in
                                               uu____8491.FStar_Syntax_Syntax.sort in
                                             FStar_Syntax_Subst.compress
                                               uu____8490 in
                                           uu____8487.FStar_Syntax_Syntax.n in
                                         match uu____8486 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8502, uu____8503::is) ->
                                             let uu____8545 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst) in
                                             FStar_All.pipe_right uu____8545
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8578 ->
                                             let uu____8579 =
                                               conjunction_t_error
                                                 "f's type is not a repr type" in
                                             FStar_Errors.raise_error
                                               uu____8579 r in
                                       FStar_List.fold_left2
                                         (fun g ->
                                            fun i1 ->
                                              fun f_i ->
                                                let uu____8595 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8595)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____8600 =
                                           let uu____8601 =
                                             let uu____8604 =
                                               let uu____8605 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst in
                                               uu____8605.FStar_Syntax_Syntax.sort in
                                             FStar_Syntax_Subst.compress
                                               uu____8604 in
                                           uu____8601.FStar_Syntax_Syntax.n in
                                         match uu____8600 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8616, uu____8617::is) ->
                                             let uu____8659 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst) in
                                             FStar_All.pipe_right uu____8659
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8692 ->
                                             let uu____8693 =
                                               conjunction_t_error
                                                 "g's type is not a repr type" in
                                             FStar_Errors.raise_error
                                               uu____8693 r in
                                       FStar_List.fold_left2
                                         (fun g ->
                                            fun i2 ->
                                              fun g_i ->
                                                let uu____8709 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8709)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body in
                                     let is =
                                       let uu____8714 =
                                         let uu____8715 =
                                           FStar_Syntax_Subst.compress body1 in
                                         uu____8715.FStar_Syntax_Syntax.n in
                                       match uu____8714 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8720, a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8775 ->
                                           let uu____8776 =
                                             conjunction_t_error
                                               "body is not a repr type" in
                                           FStar_Errors.raise_error
                                             uu____8776 r in
                                     let uu____8785 =
                                       let uu____8786 =
                                         let uu____8787 =
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
                                             uu____8787;
                                           FStar_Syntax_Syntax.flags = []
                                         } in
                                       FStar_Syntax_Syntax.mk_Comp uu____8786 in
                                     let uu____8810 =
                                       let uu____8811 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8811 g_guard in
                                     (uu____8785, uu____8810))))
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
                fun uu____8856 ->
                  let if_then_else =
                    let uu____8862 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator in
                    FStar_All.pipe_right uu____8862 FStar_Util.must in
                  let uu____8869 = destruct_wp_comp ct1 in
                  match uu____8869 with
                  | (uu____8880, uu____8881, wp_t) ->
                      let uu____8883 = destruct_wp_comp ct2 in
                      (match uu____8883 with
                       | (uu____8894, uu____8895, wp_e) ->
                           let wp =
                             let uu____8898 =
                               FStar_TypeChecker_Env.inst_effect_fun_with
                                 [u_a] env ed if_then_else in
                             let uu____8899 =
                               let uu____8900 = FStar_Syntax_Syntax.as_arg a in
                               let uu____8909 =
                                 let uu____8920 =
                                   FStar_Syntax_Syntax.as_arg p in
                                 let uu____8929 =
                                   let uu____8940 =
                                     FStar_Syntax_Syntax.as_arg wp_t in
                                   let uu____8949 =
                                     let uu____8960 =
                                       FStar_Syntax_Syntax.as_arg wp_e in
                                     [uu____8960] in
                                   uu____8940 :: uu____8949 in
                                 uu____8920 :: uu____8929 in
                               uu____8900 :: uu____8909 in
                             let uu____9009 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Syntax.mk_Tm_app uu____8898
                               uu____8899 uu____9009 in
                           let uu____9010 = mk_comp ed u_a a wp [] in
                           (uu____9010, FStar_TypeChecker_Env.trivial_guard))
let (comp_pure_wp_false :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun u ->
      fun t ->
        let post_k =
          let uu____9030 =
            let uu____9039 = FStar_Syntax_Syntax.null_binder t in
            [uu____9039] in
          let uu____9058 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
          FStar_Syntax_Util.arrow uu____9030 uu____9058 in
        let kwp =
          let uu____9064 =
            let uu____9073 = FStar_Syntax_Syntax.null_binder post_k in
            [uu____9073] in
          let uu____9092 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
          FStar_Syntax_Util.arrow uu____9064 uu____9092 in
        let post =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k in
        let wp =
          let uu____9099 =
            let uu____9100 = FStar_Syntax_Syntax.mk_binder post in
            [uu____9100] in
          let uu____9119 = fvar_const env FStar_Parser_Const.false_lid in
          FStar_Syntax_Util.abs uu____9099 uu____9119
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
            let uu____9178 =
              let uu____9179 =
                FStar_All.pipe_right scrutinee FStar_Syntax_Syntax.mk_binder in
              [uu____9179] in
            FStar_TypeChecker_Env.push_binders env0 uu____9178 in
          let eff =
            FStar_List.fold_left
              (fun eff ->
                 fun uu____9226 ->
                   match uu____9226 with
                   | (uu____9240, eff_label, uu____9242, uu____9243) ->
                       join_effects env eff eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases in
          let uu____9256 =
            let uu____9264 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu____9302 ->
                      match uu____9302 with
                      | (uu____9317, uu____9318, flags, uu____9320) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___5_9337 ->
                                  match uu___5_9337 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE ->
                                      true
                                  | uu____9340 -> false)))) in
            if uu____9264
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, []) in
          match uu____9256 with
          | (should_not_inline_whole_match, bind_cases_flags) ->
              let bind_cases uu____9377 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
                let uu____9379 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
                if uu____9379
                then
                  let uu____9386 = lax_mk_tot_or_comp_l eff u_res_t res_t [] in
                  (uu____9386, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let maybe_return eff_label_then cthen =
                     let uu____9407 =
                       should_not_inline_whole_match ||
                         (let uu____9410 = is_pure_or_ghost_effect env eff in
                          Prims.op_Negation uu____9410) in
                     if uu____9407 then cthen true else cthen false in
                   let uu____9417 =
                     let uu____9428 =
                       let uu____9441 =
                         let uu____9446 =
                           let uu____9457 =
                             FStar_All.pipe_right lcases
                               (FStar_List.map
                                  (fun uu____9507 ->
                                     match uu____9507 with
                                     | (g, uu____9526, uu____9527,
                                        uu____9528) -> g)) in
                           FStar_All.pipe_right uu____9457
                             (FStar_List.fold_left
                                (fun uu____9576 ->
                                   fun g ->
                                     match uu____9576 with
                                     | (conds, acc) ->
                                         let cond =
                                           let uu____9617 =
                                             FStar_Syntax_Util.mk_neg g in
                                           FStar_Syntax_Util.mk_conj acc
                                             uu____9617 in
                                         ((FStar_List.append conds [cond]),
                                           cond))
                                ([FStar_Syntax_Util.t_true],
                                  FStar_Syntax_Util.t_true)) in
                         FStar_All.pipe_right uu____9446
                           FStar_Pervasives_Native.fst in
                       FStar_All.pipe_right uu____9441
                         (fun l ->
                            FStar_List.splitAt
                              ((FStar_List.length l) - Prims.int_one) l) in
                     FStar_All.pipe_right uu____9428
                       (fun uu____9715 ->
                          match uu____9715 with
                          | (l1, l2) ->
                              let uu____9756 = FStar_List.hd l2 in
                              (l1, uu____9756)) in
                   match uu____9417 with
                   | (neg_branch_conds, exhaustiveness_branch_cond) ->
                       let uu____9785 =
                         match lcases with
                         | [] ->
                             let uu____9816 =
                               comp_pure_wp_false env u_res_t res_t in
                             (FStar_Pervasives_Native.None, uu____9816,
                               FStar_TypeChecker_Env.trivial_guard)
                         | uu____9819 ->
                             let uu____9836 =
                               let uu____9869 =
                                 let uu____9880 =
                                   FStar_All.pipe_right neg_branch_conds
                                     (FStar_List.splitAt
                                        ((FStar_List.length lcases) -
                                           Prims.int_one)) in
                                 FStar_All.pipe_right uu____9880
                                   (fun uu____9952 ->
                                      match uu____9952 with
                                      | (l1, l2) ->
                                          let uu____9993 = FStar_List.hd l2 in
                                          (l1, uu____9993)) in
                               match uu____9869 with
                               | (neg_branch_conds1, neg_last) ->
                                   let uu____10050 =
                                     let uu____10089 =
                                       FStar_All.pipe_right lcases
                                         (FStar_List.splitAt
                                            ((FStar_List.length lcases) -
                                               Prims.int_one)) in
                                     FStar_All.pipe_right uu____10089
                                       (fun uu____10301 ->
                                          match uu____10301 with
                                          | (l1, l2) ->
                                              let uu____10452 =
                                                FStar_List.hd l2 in
                                              (l1, uu____10452)) in
                                   (match uu____10050 with
                                    | (lcases1,
                                       (g_last, eff_last, uu____10554,
                                        c_last)) ->
                                        let uu____10624 =
                                          let lc =
                                            maybe_return eff_last c_last in
                                          let uu____10630 =
                                            FStar_TypeChecker_Common.lcomp_comp
                                              lc in
                                          match uu____10630 with
                                          | (c, g) ->
                                              let uu____10641 =
                                                let uu____10642 =
                                                  FStar_Syntax_Util.mk_conj
                                                    g_last neg_last in
                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                  g uu____10642 in
                                              (c, uu____10641) in
                                        (match uu____10624 with
                                         | (c, g) ->
                                             let uu____10677 =
                                               let uu____10678 =
                                                 FStar_All.pipe_right
                                                   eff_last
                                                   (FStar_TypeChecker_Env.norm_eff_name
                                                      env) in
                                               FStar_All.pipe_right
                                                 uu____10678
                                                 (FStar_TypeChecker_Env.get_effect_decl
                                                    env) in
                                             (lcases1, neg_branch_conds1,
                                               uu____10677, c, g))) in
                             (match uu____9836 with
                              | (lcases1, neg_branch_conds1, md, comp,
                                 g_comp) ->
                                  FStar_List.fold_right2
                                    (fun uu____10810 ->
                                       fun neg_cond ->
                                         fun uu____10812 ->
                                           match (uu____10810, uu____10812)
                                           with
                                           | ((g, eff_label, uu____10872,
                                               cthen),
                                              (uu____10874, celse, g_comp1))
                                               ->
                                               let uu____10921 =
                                                 let uu____10926 =
                                                   maybe_return eff_label
                                                     cthen in
                                                 FStar_TypeChecker_Common.lcomp_comp
                                                   uu____10926 in
                                               (match uu____10921 with
                                                | (cthen1, g_then) ->
                                                    let uu____10937 =
                                                      let uu____10948 =
                                                        lift_comps_sep_guards
                                                          env cthen1 celse
                                                          FStar_Pervasives_Native.None
                                                          false in
                                                      match uu____10948 with
                                                      | (m, cthen2, celse1,
                                                         g_lift_then,
                                                         g_lift_else) ->
                                                          let md1 =
                                                            FStar_TypeChecker_Env.get_effect_decl
                                                              env m in
                                                          let uu____10976 =
                                                            FStar_All.pipe_right
                                                              cthen2
                                                              FStar_Syntax_Util.comp_to_comp_typ in
                                                          let uu____10977 =
                                                            FStar_All.pipe_right
                                                              celse1
                                                              FStar_Syntax_Util.comp_to_comp_typ in
                                                          (md1, uu____10976,
                                                            uu____10977,
                                                            g_lift_then,
                                                            g_lift_else) in
                                                    (match uu____10937 with
                                                     | (md1, ct_then,
                                                        ct_else, g_lift_then,
                                                        g_lift_else) ->
                                                         let fn =
                                                           let uu____11028 =
                                                             FStar_All.pipe_right
                                                               md1
                                                               FStar_Syntax_Util.is_layered in
                                                           if uu____11028
                                                           then
                                                             mk_layered_conjunction
                                                           else
                                                             mk_non_layered_conjunction in
                                                         let uu____11062 =
                                                           let uu____11067 =
                                                             FStar_TypeChecker_Env.get_range
                                                               env in
                                                           fn env md1 u_res_t
                                                             res_t g ct_then
                                                             ct_else
                                                             uu____11067 in
                                                         (match uu____11062
                                                          with
                                                          | (c,
                                                             g_conjunction)
                                                              ->
                                                              let g_then1 =
                                                                let uu____11079
                                                                  =
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_then
                                                                    g_lift_then in
                                                                let uu____11080
                                                                  =
                                                                  FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    g in
                                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                                  uu____11079
                                                                  uu____11080 in
                                                              let g_else =
                                                                let uu____11082
                                                                  =
                                                                  let uu____11083
                                                                    =
                                                                    FStar_Syntax_Util.mk_neg
                                                                    g in
                                                                  FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    uu____11083 in
                                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                                  g_lift_else
                                                                  uu____11082 in
                                                              let uu____11086
                                                                =
                                                                FStar_TypeChecker_Env.conj_guards
                                                                  [g_comp1;
                                                                  g_then1;
                                                                  g_else;
                                                                  g_conjunction] in
                                                              ((FStar_Pervasives_Native.Some
                                                                  md1), c,
                                                                uu____11086)))))
                                    lcases1 neg_branch_conds1
                                    ((FStar_Pervasives_Native.Some md), comp,
                                      g_comp)) in
                       (match uu____9785 with
                        | (md, comp, g_comp) ->
                            let uu____11102 =
                              let uu____11107 =
                                let check =
                                  FStar_Syntax_Util.mk_imp
                                    exhaustiveness_branch_cond
                                    FStar_Syntax_Util.t_false in
                                let check1 =
                                  let uu____11114 =
                                    FStar_TypeChecker_Env.get_range env in
                                  label
                                    FStar_TypeChecker_Err.exhaustiveness_check
                                    uu____11114 check in
                                strengthen_comp env
                                  FStar_Pervasives_Native.None comp check1
                                  bind_cases_flags in
                              match uu____11107 with
                              | (c, g) ->
                                  let uu____11125 =
                                    FStar_TypeChecker_Env.conj_guard g_comp g in
                                  (c, uu____11125) in
                            (match uu____11102 with
                             | (comp1, g_comp1) ->
                                 let g_comp2 =
                                   let uu____11133 =
                                     let uu____11134 =
                                       FStar_All.pipe_right scrutinee
                                         FStar_Syntax_Syntax.mk_binder in
                                     [uu____11134] in
                                   FStar_TypeChecker_Env.close_guard env0
                                     uu____11133 g_comp1 in
                                 (match lcases with
                                  | [] -> (comp1, g_comp2)
                                  | uu____11177::[] -> (comp1, g_comp2)
                                  | uu____11220 ->
                                      let uu____11237 =
                                        let uu____11239 =
                                          FStar_All.pipe_right md
                                            FStar_Util.must in
                                        FStar_All.pipe_right uu____11239
                                          FStar_Syntax_Util.is_layered in
                                      if uu____11237
                                      then (comp1, g_comp2)
                                      else
                                        (let comp2 =
                                           FStar_TypeChecker_Env.comp_to_comp_typ
                                             env comp1 in
                                         let md1 =
                                           FStar_TypeChecker_Env.get_effect_decl
                                             env
                                             comp2.FStar_Syntax_Syntax.effect_name in
                                         let uu____11252 =
                                           destruct_wp_comp comp2 in
                                         match uu____11252 with
                                         | (uu____11263, uu____11264, wp) ->
                                             let ite_wp =
                                               let uu____11267 =
                                                 FStar_All.pipe_right md1
                                                   FStar_Syntax_Util.get_wp_ite_combinator in
                                               FStar_All.pipe_right
                                                 uu____11267 FStar_Util.must in
                                             let wp1 =
                                               let uu____11275 =
                                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                                   [u_res_t] env md1 ite_wp in
                                               let uu____11276 =
                                                 let uu____11277 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     res_t in
                                                 let uu____11286 =
                                                   let uu____11297 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp in
                                                   [uu____11297] in
                                                 uu____11277 :: uu____11286 in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu____11275 uu____11276
                                                 wp.FStar_Syntax_Syntax.pos in
                                             let uu____11330 =
                                               mk_comp md1 u_res_t res_t wp1
                                                 bind_cases_flags in
                                             (uu____11330, g_comp2)))))) in
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
          let uu____11365 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____11365 with
          | FStar_Pervasives_Native.None ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____11381 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c' in
                let uu____11387 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error uu____11381 uu____11387
              else
                (let uu____11396 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c' in
                 let uu____11402 = FStar_TypeChecker_Env.get_range env in
                 FStar_Errors.raise_error uu____11396 uu____11402)
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
          let uu____11427 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name in
          FStar_All.pipe_right uu____11427
            (FStar_TypeChecker_Env.norm_eff_name env) in
        let uu____11430 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid in
        if uu____11430
        then u_res
        else
          (let is_total =
             let uu____11437 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid in
             FStar_All.pipe_right uu____11437
               (FStar_List.existsb
                  (fun q -> q = FStar_Syntax_Syntax.TotalEffect)) in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____11448 = FStar_TypeChecker_Env.effect_repr env c u_res in
              match uu____11448 with
              | FStar_Pervasives_Native.None ->
                  let uu____11451 =
                    let uu____11457 =
                      let uu____11459 =
                        FStar_Syntax_Print.lid_to_string c_lid in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____11459 in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____11457) in
                  FStar_Errors.raise_error uu____11451
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
      let uu____11483 = destruct_wp_comp ct in
      match uu____11483 with
      | (u_t, t, wp) ->
          let vc =
            let uu____11500 =
              let uu____11501 =
                let uu____11502 =
                  FStar_All.pipe_right md
                    FStar_Syntax_Util.get_wp_trivial_combinator in
                FStar_All.pipe_right uu____11502 FStar_Util.must in
              FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                uu____11501 in
            let uu____11509 =
              let uu____11510 = FStar_Syntax_Syntax.as_arg t in
              let uu____11519 =
                let uu____11530 = FStar_Syntax_Syntax.as_arg wp in
                [uu____11530] in
              uu____11510 :: uu____11519 in
            let uu____11563 = FStar_TypeChecker_Env.get_range env in
            FStar_Syntax_Syntax.mk_Tm_app uu____11500 uu____11509 uu____11563 in
          let uu____11564 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc) in
          (ct, vc, uu____11564)
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
                  let uu____11619 =
                    FStar_TypeChecker_Env.try_lookup_lid env f in
                  match uu____11619 with
                  | FStar_Pervasives_Native.Some uu____11634 ->
                      ((let uu____11652 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions") in
                        if uu____11652
                        then
                          let uu____11656 = FStar_Ident.string_of_lid f in
                          FStar_Util.print1 "Coercing with %s!\n" uu____11656
                        else ());
                       (let coercion =
                          let uu____11662 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos in
                          FStar_Syntax_Syntax.fvar uu____11662
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs in
                        let lc1 =
                          let uu____11669 =
                            let uu____11670 =
                              let uu____11671 = mkcomp ty in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____11671 in
                            (FStar_Pervasives_Native.None, uu____11670) in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____11669 in
                        let e1 =
                          let uu____11675 =
                            let uu____11676 = FStar_Syntax_Syntax.as_arg e in
                            [uu____11676] in
                          FStar_Syntax_Syntax.mk_Tm_app coercion2 uu____11675
                            e.FStar_Syntax_Syntax.pos in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None ->
                      ((let uu____11710 =
                          let uu____11716 =
                            let uu____11718 = FStar_Ident.string_of_lid f in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____11718 in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____11716) in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____11710);
                       (e, lc))
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee ->
    match projectee with | Yes _0 -> true | uu____11737 -> false
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee -> match projectee with | Yes _0 -> _0
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee ->
    match projectee with | Maybe -> true | uu____11755 -> false
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee -> match projectee with | No -> true | uu____11766 -> false
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
      let uu____11790 = FStar_Syntax_Util.head_and_args t2 in
      match uu____11790 with
      | (h, args) ->
          let h1 = FStar_Syntax_Util.un_uinst h in
          let r =
            let uu____11835 =
              let uu____11850 =
                let uu____11851 = FStar_Syntax_Subst.compress h1 in
                uu____11851.FStar_Syntax_Syntax.n in
              (uu____11850, args) in
            match uu____11835 with
            | (FStar_Syntax_Syntax.Tm_fvar fv,
               (a, FStar_Pervasives_Native.None)::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____11898, uu____11899) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown, uu____11932) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match (uu____11953, branches),
               uu____11955) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc ->
                        fun br ->
                          match acc with
                          | Yes uu____12019 -> Maybe
                          | Maybe -> Maybe
                          | No ->
                              let uu____12020 =
                                FStar_Syntax_Subst.open_branch br in
                              (match uu____12020 with
                               | (uu____12021, uu____12022, br_body) ->
                                   let uu____12040 =
                                     let uu____12041 =
                                       let uu____12046 =
                                         let uu____12047 =
                                           let uu____12050 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names in
                                           FStar_All.pipe_right uu____12050
                                             FStar_Util.set_elements in
                                         FStar_All.pipe_right uu____12047
                                           (FStar_TypeChecker_Env.push_bvs
                                              env) in
                                       check_erased uu____12046 in
                                     FStar_All.pipe_right br_body uu____12041 in
                                   (match uu____12040 with
                                    | No -> No
                                    | uu____12061 -> Maybe))) No)
            | uu____12062 -> No in
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
            (((let uu____12114 = FStar_Options.use_two_phase_tc () in
               Prims.op_Negation uu____12114) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ()) in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
               let uu____12133 =
                 let uu____12134 = FStar_Syntax_Subst.compress t1 in
                 uu____12134.FStar_Syntax_Syntax.n in
               match uu____12133 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____12139 -> false in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
               let uu____12149 =
                 let uu____12150 = FStar_Syntax_Subst.compress t1 in
                 uu____12150.FStar_Syntax_Syntax.n in
               match uu____12149 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____12155 -> false in
             let is_type t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
               let t2 = FStar_Syntax_Util.unrefine t1 in
               let uu____12166 =
                 let uu____12167 = FStar_Syntax_Subst.compress t2 in
                 uu____12167.FStar_Syntax_Syntax.n in
               match uu____12166 with
               | FStar_Syntax_Syntax.Tm_type uu____12171 -> true
               | uu____12173 -> false in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ in
             let uu____12176 = FStar_Syntax_Util.head_and_args res_typ in
             match uu____12176 with
             | (head, args) ->
                 ((let uu____12226 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions") in
                   if uu____12226
                   then
                     let uu____12230 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                     let uu____12232 = FStar_Syntax_Print.term_to_string e in
                     let uu____12234 =
                       FStar_Syntax_Print.term_to_string res_typ in
                     let uu____12236 =
                       FStar_Syntax_Print.term_to_string exp_t in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____12230 uu____12232 uu____12234 uu____12236
                   else ());
                  (let mk_erased u t =
                     let uu____12254 =
                       let uu____12257 =
                         fvar_const env FStar_Parser_Const.erased_lid in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____12257 [u] in
                     let uu____12258 =
                       let uu____12269 = FStar_Syntax_Syntax.as_arg t in
                       [uu____12269] in
                     FStar_Syntax_Util.mk_app uu____12254 uu____12258 in
                   let uu____12294 =
                     let uu____12309 =
                       let uu____12310 = FStar_Syntax_Util.un_uinst head in
                       uu____12310.FStar_Syntax_Syntax.n in
                     (uu____12309, args) in
                   match uu____12294 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type exp_t)
                       ->
                       let uu____12348 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total in
                       (match uu____12348 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____12388 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac in
                       (match uu____12388 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____12428 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac in
                       (match uu____12428 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____12468 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac in
                       (match uu____12468 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____12489 ->
                       let uu____12504 =
                         let uu____12509 = check_erased env res_typ in
                         let uu____12510 = check_erased env exp_t in
                         (uu____12509, uu____12510) in
                       (match uu____12504 with
                        | (No, Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty in
                            let uu____12519 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty in
                            (match uu____12519 with
                             | FStar_Pervasives_Native.None ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e in
                                 let uu____12530 =
                                   let uu____12535 =
                                     let uu____12536 =
                                       FStar_Syntax_Syntax.iarg ty in
                                     [uu____12536] in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____12535
                                     FStar_Syntax_Syntax.mk_Total in
                                 (match uu____12530 with
                                  | (e1, lc1) -> (e1, lc1, g1)))
                        | (Yes ty, No) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty in
                            let uu____12571 =
                              let uu____12576 =
                                let uu____12577 = FStar_Syntax_Syntax.iarg ty in
                                [uu____12577] in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____12576
                                FStar_Syntax_Syntax.mk_GTotal in
                            (match uu____12571 with
                             | (e1, lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____12610 ->
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
        let uu____12645 = FStar_Syntax_Util.head_and_args rt1 in
        match uu____12645 with
        | (hd, args) ->
            let uu____12694 =
              let uu____12709 =
                let uu____12710 = FStar_Syntax_Subst.compress hd in
                uu____12710.FStar_Syntax_Syntax.n in
              (uu____12709, args) in
            (match uu____12694 with
             | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____12748 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac in
                 FStar_All.pipe_left
                   (fun uu____12775 ->
                      FStar_Pervasives_Native.Some uu____12775) uu____12748
             | uu____12776 -> FStar_Pervasives_Native.None)
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
          (let uu____12829 =
             FStar_TypeChecker_Env.debug env FStar_Options.High in
           if uu____12829
           then
             let uu____12832 = FStar_Syntax_Print.term_to_string e in
             let uu____12834 = FStar_TypeChecker_Common.lcomp_to_string lc in
             let uu____12836 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____12832 uu____12834 uu____12836
           else ());
          (let use_eq =
             (env.FStar_TypeChecker_Env.use_eq_strict ||
                env.FStar_TypeChecker_Env.use_eq)
               ||
               (let uu____12846 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name in
                match uu____12846 with
                | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____12871 -> false) in
           let gopt =
             if use_eq
             then
               let uu____12897 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t in
               (uu____12897, false)
             else
               (let uu____12907 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t in
                (uu____12907, true)) in
           match gopt with
           | (FStar_Pervasives_Native.None, uu____12920) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____12932 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ in
                 FStar_Errors.raise_error uu____12932
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1442_12948 = lc in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1442_12948.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1442_12948.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1442_12948.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g, apply_guard) ->
               let uu____12955 = FStar_TypeChecker_Env.guard_form g in
               (match uu____12955 with
                | FStar_TypeChecker_Common.Trivial ->
                    let strengthen_trivial uu____12971 =
                      let uu____12972 =
                        FStar_TypeChecker_Common.lcomp_comp lc in
                      match uu____12972 with
                      | (c, g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c in
                          let set_result_typ c1 =
                            FStar_Syntax_Util.set_result_typ c1 t in
                          let uu____12992 =
                            let uu____12994 = FStar_Syntax_Util.eq_tm t res_t in
                            uu____12994 = FStar_Syntax_Util.Equal in
                          if uu____12992
                          then
                            ((let uu____13001 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____13001
                              then
                                let uu____13005 =
                                  FStar_Syntax_Print.term_to_string res_t in
                                let uu____13007 =
                                  FStar_Syntax_Print.term_to_string t in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____13005 uu____13007
                              else ());
                             (let uu____13012 = set_result_typ c in
                              (uu____13012, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____13019 ->
                                   true
                               | uu____13027 -> false in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t in
                               let cret =
                                 let uu____13036 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____13036 in
                               let lc1 =
                                 let uu____13038 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c in
                                 let uu____13039 =
                                   let uu____13040 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____13040) in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____13038 uu____13039 in
                               ((let uu____13044 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____13044
                                 then
                                   let uu____13048 =
                                     FStar_Syntax_Print.term_to_string e in
                                   let uu____13050 =
                                     FStar_Syntax_Print.comp_to_string c in
                                   let uu____13052 =
                                     FStar_Syntax_Print.term_to_string t in
                                   let uu____13054 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1 in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____13048 uu____13050 uu____13052
                                     uu____13054
                                 else ());
                                (let uu____13059 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1 in
                                 match uu____13059 with
                                 | (c1, g_lc) ->
                                     let uu____13070 = set_result_typ c1 in
                                     let uu____13071 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc in
                                     (uu____13070, uu____13071)))
                             else
                               ((let uu____13075 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____13075
                                 then
                                   let uu____13079 =
                                     FStar_Syntax_Print.term_to_string res_t in
                                   let uu____13081 =
                                     FStar_Syntax_Print.comp_to_string c in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____13079 uu____13081
                                 else ());
                                (let uu____13086 = set_result_typ c in
                                 (uu____13086, g_c)))) in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1479_13090 = g in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred_to_tac =
                          (uu___1479_13090.FStar_TypeChecker_Common.deferred_to_tac);
                        FStar_TypeChecker_Common.deferred =
                          (uu___1479_13090.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1479_13090.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1479_13090.FStar_TypeChecker_Common.implicits)
                      } in
                    let strengthen uu____13100 =
                      let uu____13101 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ()) in
                      if uu____13101
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f in
                         let uu____13111 =
                           let uu____13112 = FStar_Syntax_Subst.compress f1 in
                           uu____13112.FStar_Syntax_Syntax.n in
                         match uu____13111 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____13119,
                              {
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Tm_fvar fv;
                                FStar_Syntax_Syntax.pos = uu____13121;
                                FStar_Syntax_Syntax.vars = uu____13122;_},
                              uu____13123)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1495_13149 = lc in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1495_13149.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1495_13149.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1495_13149.FStar_TypeChecker_Common.comp_thunk)
                               } in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____13150 ->
                             let uu____13151 =
                               FStar_TypeChecker_Common.lcomp_comp lc in
                             (match uu____13151 with
                              | (c, g_c) ->
                                  ((let uu____13163 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme in
                                    if uu____13163
                                    then
                                      let uu____13167 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ in
                                      let uu____13169 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t in
                                      let uu____13171 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c in
                                      let uu____13173 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1 in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____13167 uu____13169 uu____13171
                                        uu____13173
                                    else ());
                                   (let u_t_opt = comp_univ_opt c in
                                    let x =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (t.FStar_Syntax_Syntax.pos)) t in
                                    let xexp =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let cret =
                                      return_value env u_t_opt t xexp in
                                    let guard =
                                      if apply_guard
                                      then
                                        let uu____13186 =
                                          let uu____13187 =
                                            FStar_Syntax_Syntax.as_arg xexp in
                                          [uu____13187] in
                                        FStar_Syntax_Syntax.mk_Tm_app f1
                                          uu____13186
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1 in
                                    let uu____13214 =
                                      let uu____13219 =
                                        FStar_All.pipe_left
                                          (fun uu____13240 ->
                                             FStar_Pervasives_Native.Some
                                               uu____13240)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t) in
                                      let uu____13241 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos in
                                      let uu____13242 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret in
                                      let uu____13243 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard) in
                                      strengthen_precondition uu____13219
                                        uu____13241 e uu____13242 uu____13243 in
                                    match uu____13214 with
                                    | (eq_ret, _trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1513_13251 = x in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1513_13251.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1513_13251.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          } in
                                        let c1 =
                                          let uu____13253 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____13253
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret) in
                                        let uu____13256 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1 in
                                        (match uu____13256 with
                                         | (c2, g_lc) ->
                                             ((let uu____13268 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme in
                                               if uu____13268
                                               then
                                                 let uu____13272 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2 in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____13272
                                               else ());
                                              (let uu____13277 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc in
                                               (c2, uu____13277)))))))) in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_13286 ->
                              match uu___6_13286 with
                              | FStar_Syntax_Syntax.RETURN ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____13289 -> [])) in
                    let lc1 =
                      let uu____13291 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name in
                      FStar_TypeChecker_Common.mk_lcomp uu____13291 t flags
                        strengthen in
                    let g2 =
                      let uu___1529_13293 = g1 in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred_to_tac =
                          (uu___1529_13293.FStar_TypeChecker_Common.deferred_to_tac);
                        FStar_TypeChecker_Common.deferred =
                          (uu___1529_13293.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1529_13293.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1529_13293.FStar_TypeChecker_Common.implicits)
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
        let uu____13329 =
          let uu____13332 =
            let uu____13333 =
              let uu____13342 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_Syntax_Syntax.as_arg uu____13342 in
            [uu____13333] in
          FStar_Syntax_Syntax.mk_Tm_app ens uu____13332
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____13329 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t in
      let uu____13365 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____13365
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____13384 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____13400 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____13417 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid) in
             if uu____13417
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req, uu____13433)::(ens, uu____13435)::uu____13436 ->
                    let uu____13479 =
                      let uu____13482 = norm req in
                      FStar_Pervasives_Native.Some uu____13482 in
                    let uu____13483 =
                      let uu____13484 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____13484 in
                    (uu____13479, uu____13483)
                | uu____13487 ->
                    let uu____13498 =
                      let uu____13504 =
                        let uu____13506 =
                          FStar_Syntax_Print.comp_to_string comp in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____13506 in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____13504) in
                    FStar_Errors.raise_error uu____13498
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp, uu____13526)::uu____13527 ->
                    let uu____13554 =
                      let uu____13559 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____13559 in
                    (match uu____13554 with
                     | (us_r, uu____13591) ->
                         let uu____13592 =
                           let uu____13597 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____13597 in
                         (match uu____13592 with
                          | (us_e, uu____13629) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____13632 =
                                  let uu____13633 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r in
                                  FStar_Syntax_Syntax.fvar uu____13633
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____13632
                                  us_r in
                              let as_ens =
                                let uu____13635 =
                                  let uu____13636 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r in
                                  FStar_Syntax_Syntax.fvar uu____13636
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____13635
                                  us_e in
                              let req =
                                let uu____13638 =
                                  let uu____13639 =
                                    let uu____13650 =
                                      FStar_Syntax_Syntax.as_arg wp in
                                    [uu____13650] in
                                  ((ct1.FStar_Syntax_Syntax.result_typ),
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.imp_tag))
                                    :: uu____13639 in
                                FStar_Syntax_Syntax.mk_Tm_app as_req
                                  uu____13638
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____13688 =
                                  let uu____13689 =
                                    let uu____13700 =
                                      FStar_Syntax_Syntax.as_arg wp in
                                    [uu____13700] in
                                  ((ct1.FStar_Syntax_Syntax.result_typ),
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.imp_tag))
                                    :: uu____13689 in
                                FStar_Syntax_Syntax.mk_Tm_app as_ens
                                  uu____13688
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____13737 =
                                let uu____13740 = norm req in
                                FStar_Pervasives_Native.Some uu____13740 in
                              let uu____13741 =
                                let uu____13742 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____13742 in
                              (uu____13737, uu____13741)))
                | uu____13745 -> failwith "Impossible"))
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
        (let uu____13784 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____13784
         then
           let uu____13789 = FStar_Syntax_Print.term_to_string tm in
           let uu____13791 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____13789
             uu____13791
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
          (let uu____13850 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify") in
           if uu____13850
           then
             let uu____13855 = FStar_Syntax_Print.term_to_string tm in
             let uu____13857 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____13855
               uu____13857
           else ());
          tm'
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____13868 =
      let uu____13870 =
        let uu____13871 = FStar_Syntax_Subst.compress t in
        uu____13871.FStar_Syntax_Syntax.n in
      match uu____13870 with
      | FStar_Syntax_Syntax.Tm_app uu____13875 -> false
      | uu____13893 -> true in
    if uu____13868
    then t
    else
      (let uu____13898 = FStar_Syntax_Util.head_and_args t in
       match uu____13898 with
       | (head, args) ->
           let uu____13941 =
             let uu____13943 =
               let uu____13944 = FStar_Syntax_Subst.compress head in
               uu____13944.FStar_Syntax_Syntax.n in
             match uu____13943 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) ->
                 true
             | uu____13949 -> false in
           if uu____13941
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____13981 ->
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
          ((let uu____14028 =
              FStar_TypeChecker_Env.debug env FStar_Options.High in
            if uu____14028
            then
              let uu____14031 = FStar_Syntax_Print.term_to_string e in
              let uu____14033 = FStar_Syntax_Print.term_to_string t in
              let uu____14035 =
                let uu____14037 = FStar_TypeChecker_Env.expected_typ env in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____14037 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____14031 uu____14033 uu____14035
            else ());
           (let unfolded_arrow_formals t1 =
              let rec aux bs t2 =
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf env t2 in
                let uu____14073 = FStar_Syntax_Util.arrow_formals t3 in
                match uu____14073 with
                | (bs', t4) ->
                    (match bs' with
                     | [] -> bs
                     | bs'1 -> aux (FStar_List.append bs bs'1) t4) in
              aux [] t1 in
            let number_of_implicits t1 =
              let formals = unfolded_arrow_formals t1 in
              let n_implicits =
                let uu____14107 =
                  FStar_All.pipe_right formals
                    (FStar_Util.prefix_until
                       (fun uu____14185 ->
                          match uu____14185 with
                          | (uu____14193, imp) ->
                              (FStar_Option.isNone imp) ||
                                (let uu____14200 =
                                   FStar_Syntax_Util.eq_aqual imp
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Equality) in
                                 uu____14200 = FStar_Syntax_Util.Equal))) in
                match uu____14107 with
                | FStar_Pervasives_Native.None -> FStar_List.length formals
                | FStar_Pervasives_Native.Some
                    (implicits, _first_explicit, _rest) ->
                    FStar_List.length implicits in
              n_implicits in
            let inst_n_binders t1 =
              let uu____14319 = FStar_TypeChecker_Env.expected_typ env in
              match uu____14319 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t in
                  let n_available = number_of_implicits t1 in
                  if n_available < n_expected
                  then
                    let uu____14333 =
                      let uu____14339 =
                        let uu____14341 = FStar_Util.string_of_int n_expected in
                        let uu____14343 = FStar_Syntax_Print.term_to_string e in
                        let uu____14345 =
                          FStar_Util.string_of_int n_available in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____14341 uu____14343 uu____14345 in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____14339) in
                    let uu____14349 = FStar_TypeChecker_Env.get_range env in
                    FStar_Errors.raise_error uu____14333 uu____14349
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected) in
            let decr_inst uu___7_14367 =
              match uu___7_14367 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one) in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                let uu____14410 = FStar_Syntax_Subst.open_comp bs c in
                (match uu____14410 with
                 | (bs1, c1) ->
                     let rec aux subst inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some uu____14541,
                          uu____14528) when uu____14541 = Prims.int_zero ->
                           ([], bs2, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____14574,
                          (x, FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit uu____14576))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort in
                           let uu____14610 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2 in
                           (match uu____14610 with
                            | (v, uu____14651, g) ->
                                ((let uu____14666 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High in
                                  if uu____14666
                                  then
                                    let uu____14669 =
                                      FStar_Syntax_Print.term_to_string v in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____14669
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst in
                                  let uu____14679 =
                                    aux subst1 (decr_inst inst_n) rest in
                                  match uu____14679 with
                                  | (args, bs3, subst2, g') ->
                                      let uu____14772 =
                                        FStar_TypeChecker_Env.conj_guard g g' in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____14772))))
                       | (uu____14799,
                          (x, FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tac_or_attr))::rest) ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort in
                           let meta_t =
                             match tac_or_attr with
                             | FStar_Syntax_Syntax.Arg_qualifier_meta_tac tau
                                 ->
                                 let uu____14838 =
                                   let uu____14845 = FStar_Dyn.mkdyn env in
                                   (uu____14845, tau) in
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   uu____14838
                             | FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                 attr ->
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_attr attr in
                           let uu____14851 =
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict
                               (FStar_Pervasives_Native.Some meta_t) in
                           (match uu____14851 with
                            | (v, uu____14892, g) ->
                                ((let uu____14907 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High in
                                  if uu____14907
                                  then
                                    let uu____14910 =
                                      FStar_Syntax_Print.term_to_string v in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____14910
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst in
                                  let uu____14920 =
                                    aux subst1 (decr_inst inst_n) rest in
                                  match uu____14920 with
                                  | (args, bs3, subst2, g') ->
                                      let uu____15013 =
                                        FStar_TypeChecker_Env.conj_guard g g' in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____15013))))
                       | (uu____15040, bs3) ->
                           ([], bs3, subst,
                             FStar_TypeChecker_Env.trivial_guard) in
                     let uu____15088 =
                       let uu____15115 = inst_n_binders t1 in
                       aux [] uu____15115 bs1 in
                     (match uu____15088 with
                      | (args, bs2, subst, guard) ->
                          (match (args, bs2) with
                           | ([], uu____15187) -> (e, torig, guard)
                           | (uu____15218, []) when
                               let uu____15249 =
                                 FStar_Syntax_Util.is_total_comp c1 in
                               Prims.op_Negation uu____15249 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____15251 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____15279 ->
                                     FStar_Syntax_Util.arrow bs2 c1 in
                               let t3 = FStar_Syntax_Subst.subst subst t2 in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   e.FStar_Syntax_Syntax.pos in
                               (e1, t3, guard))))
            | uu____15290 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs ->
    let uu____15302 =
      let uu____15306 = FStar_Util.set_elements univs in
      FStar_All.pipe_right uu____15306
        (FStar_List.map
           (fun u ->
              let uu____15318 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____15318 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____15302 (FStar_String.concat ", ")
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env ->
    fun x ->
      let uu____15346 = FStar_Util.set_is_empty x in
      if uu____15346
      then []
      else
        (let s =
           let uu____15366 =
             let uu____15369 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____15369 in
           FStar_All.pipe_right uu____15366 FStar_Util.set_elements in
         (let uu____15387 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____15387
          then
            let uu____15392 =
              let uu____15394 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____15394 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____15392
          else ());
         (let r =
            let uu____15403 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____15403 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____15448 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____15448
                     then
                       let uu____15453 =
                         let uu____15455 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____15455 in
                       let uu____15459 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____15461 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____15453 uu____15459 uu____15461
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
        let uu____15491 =
          FStar_Util.set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____15491 FStar_Util.set_elements in
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
        | ([], uu____15530) -> generalized_univ_names
        | (uu____15537, []) -> explicit_univ_names
        | uu____15544 ->
            let uu____15553 =
              let uu____15559 =
                let uu____15561 = FStar_Syntax_Print.term_to_string t in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____15561 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____15559) in
            FStar_Errors.raise_error uu____15553 t.FStar_Syntax_Syntax.pos
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
      (let uu____15583 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____15583
       then
         let uu____15588 = FStar_Syntax_Print.term_to_string t in
         let uu____15590 = FStar_Syntax_Print.univ_names_to_string univnames in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____15588 uu____15590
       else ());
      (let univs = FStar_Syntax_Free.univs t in
       (let uu____15599 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____15599
        then
          let uu____15604 = string_of_univs univs in
          FStar_Util.print1 "univs to gen : %s\n" uu____15604
        else ());
       (let gen = gen_univs env univs in
        (let uu____15613 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen") in
         if uu____15613
         then
           let uu____15618 = FStar_Syntax_Print.term_to_string t in
           let uu____15620 = FStar_Syntax_Print.univ_names_to_string gen in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____15618 uu____15620
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
        let uu____15704 =
          let uu____15706 =
            FStar_Util.for_all
              (fun uu____15720 ->
                 match uu____15720 with
                 | (uu____15730, uu____15731, c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          FStar_All.pipe_left Prims.op_Negation uu____15706 in
        if uu____15704
        then FStar_Pervasives_Native.None
        else
          (let norm c =
             (let uu____15783 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              if uu____15783
              then
                let uu____15786 = FStar_Syntax_Print.comp_to_string c in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____15786
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c in
              (let uu____15793 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____15793
               then
                 let uu____15796 = FStar_Syntax_Print.comp_to_string c1 in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____15796
               else ());
              c1) in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu____15814 = FStar_Util.set_difference uvs env_uvars in
             FStar_All.pipe_right uu____15814 FStar_Util.set_elements in
           let univs_and_uvars_of_lec uu____15848 =
             match uu____15848 with
             | (lbname, e, c) ->
                 let c1 = norm c in
                 let t = FStar_Syntax_Util.comp_result c1 in
                 let univs = FStar_Syntax_Free.univs t in
                 let uvt = FStar_Syntax_Free.uvars t in
                 ((let uu____15885 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen") in
                   if uu____15885
                   then
                     let uu____15890 =
                       let uu____15892 =
                         let uu____15896 = FStar_Util.set_elements univs in
                         FStar_All.pipe_right uu____15896
                           (FStar_List.map
                              (fun u ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u))) in
                       FStar_All.pipe_right uu____15892
                         (FStar_String.concat ", ") in
                     let uu____15952 =
                       let uu____15954 =
                         let uu____15958 = FStar_Util.set_elements uvt in
                         FStar_All.pipe_right uu____15958
                           (FStar_List.map
                              (fun u ->
                                 let uu____15971 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head in
                                 let uu____15973 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                 FStar_Util.format2 "(%s : %s)" uu____15971
                                   uu____15973)) in
                       FStar_All.pipe_right uu____15954
                         (FStar_String.concat ", ") in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____15890
                       uu____15952
                   else ());
                  (let univs1 =
                     let uu____15987 = FStar_Util.set_elements uvt in
                     FStar_List.fold_left
                       (fun univs1 ->
                          fun uv ->
                            let uu____15999 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ in
                            FStar_Util.set_union univs1 uu____15999) univs
                       uu____15987 in
                   let uvs = gen_uvars uvt in
                   (let uu____16006 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen") in
                    if uu____16006
                    then
                      let uu____16011 =
                        let uu____16013 =
                          let uu____16017 = FStar_Util.set_elements univs1 in
                          FStar_All.pipe_right uu____16017
                            (FStar_List.map
                               (fun u ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u))) in
                        FStar_All.pipe_right uu____16013
                          (FStar_String.concat ", ") in
                      let uu____16073 =
                        let uu____16075 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u ->
                                  let uu____16089 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head in
                                  let uu____16091 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                  FStar_Util.format2 "(%s : %s)" uu____16089
                                    uu____16091)) in
                        FStar_All.pipe_right uu____16075
                          (FStar_String.concat ", ") in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____16011 uu____16073
                    else ());
                   (univs1, uvs, (lbname, e, c1)))) in
           let uu____16112 =
             let uu____16129 = FStar_List.hd lecs in
             univs_and_uvars_of_lec uu____16129 in
           match uu____16112 with
           | (univs, uvs, lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____16219 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1) in
                 if uu____16219
                 then ()
                 else
                   (let uu____16224 = lec_hd in
                    match uu____16224 with
                    | (lb1, uu____16232, uu____16233) ->
                        let uu____16234 = lec2 in
                        (match uu____16234 with
                         | (lb2, uu____16242, uu____16243) ->
                             let msg =
                               let uu____16246 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____16248 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____16246 uu____16248 in
                             let uu____16251 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____16251)) in
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
                 let uu____16319 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1) in
                 if uu____16319
                 then ()
                 else
                   (let uu____16324 = lec_hd in
                    match uu____16324 with
                    | (lb1, uu____16332, uu____16333) ->
                        let uu____16334 = lec2 in
                        (match uu____16334 with
                         | (lb2, uu____16342, uu____16343) ->
                             let msg =
                               let uu____16346 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____16348 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____16346 uu____16348 in
                             let uu____16351 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____16351)) in
               let lecs1 =
                 let uu____16362 = FStar_List.tl lecs in
                 FStar_List.fold_right
                   (fun this_lec ->
                      fun lecs1 ->
                        let uu____16415 = univs_and_uvars_of_lec this_lec in
                        match uu____16415 with
                        | (this_univs, this_uvs, this_lec1) ->
                            (force_univs_eq this_lec1 univs this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____16362 [] in
               let lecs2 = lec_hd :: lecs1 in
               let gen_types uvs1 =
                 let fail rng k =
                   let uu____16525 = lec_hd in
                   match uu____16525 with
                   | (lbname, e, c) ->
                       let uu____16535 =
                         let uu____16541 =
                           let uu____16543 =
                             FStar_Syntax_Print.term_to_string k in
                           let uu____16545 =
                             FStar_Syntax_Print.lbname_to_string lbname in
                           let uu____16547 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c) in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____16543 uu____16545 uu____16547 in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____16541) in
                       FStar_Errors.raise_error uu____16535 rng in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u ->
                         let uu____16569 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head in
                         match uu____16569 with
                         | FStar_Pervasives_Native.Some uu____16578 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____16586 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ in
                             let uu____16590 =
                               FStar_Syntax_Util.arrow_formals k in
                             (match uu____16590 with
                              | (bs, kres) ->
                                  ((let uu____16610 =
                                      let uu____16611 =
                                        let uu____16614 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres in
                                        FStar_Syntax_Util.unrefine
                                          uu____16614 in
                                      uu____16611.FStar_Syntax_Syntax.n in
                                    match uu____16610 with
                                    | FStar_Syntax_Syntax.Tm_type uu____16615
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres in
                                        let uu____16619 =
                                          let uu____16621 =
                                            FStar_Util.set_is_empty free in
                                          Prims.op_Negation uu____16621 in
                                        if uu____16619
                                        then
                                          fail
                                            u.FStar_Syntax_Syntax.ctx_uvar_range
                                            kres
                                        else ()
                                    | uu____16626 ->
                                        fail
                                          u.FStar_Syntax_Syntax.ctx_uvar_range
                                          kres);
                                   (let a =
                                      let uu____16628 =
                                        let uu____16631 =
                                          FStar_TypeChecker_Env.get_range env in
                                        FStar_All.pipe_left
                                          (fun uu____16634 ->
                                             FStar_Pervasives_Native.Some
                                               uu____16634) uu____16631 in
                                      FStar_Syntax_Syntax.new_bv uu____16628
                                        kres in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____16642 ->
                                          let uu____16643 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Util.abs bs
                                            uu____16643
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
                      (fun uu____16746 ->
                         match uu____16746 with
                         | (lbname, e, c) ->
                             let uu____16792 =
                               match (gen_tvars, gen_univs1) with
                               | ([], []) -> (e, c, [])
                               | uu____16853 ->
                                   let uu____16866 = (e, c) in
                                   (match uu____16866 with
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
                                                (fun uu____16906 ->
                                                   match uu____16906 with
                                                   | (x, uu____16912) ->
                                                       let uu____16913 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____16913)
                                                gen_tvars in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____16931 =
                                                let uu____16933 =
                                                  FStar_Util.right lbname in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____16933 in
                                              if uu____16931
                                              then
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  tm tvar_args
                                                  tm.FStar_Syntax_Syntax.pos
                                              else tm in
                                            FStar_Syntax_InstFV.inst
                                              instantiate_lbname_with_app e1
                                          else e1 in
                                        let t =
                                          let uu____16942 =
                                            let uu____16943 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____16943.FStar_Syntax_Syntax.n in
                                          match uu____16942 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs, cod) ->
                                              let uu____16968 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____16968 with
                                               | (bs1, cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____16979 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____16983 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____16983, gen_tvars)) in
                             (match uu____16792 with
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
        (let uu____17130 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____17130
         then
           let uu____17133 =
             let uu____17135 =
               FStar_List.map
                 (fun uu____17150 ->
                    match uu____17150 with
                    | (lb, uu____17159, uu____17160) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_All.pipe_right uu____17135 (FStar_String.concat ", ") in
           FStar_Util.print1 "Generalizing: %s\n" uu____17133
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____17186 ->
                match uu____17186 with
                | (l, t, c) -> gather_free_univnames env t) lecs in
         let generalized_lecs =
           let uu____17215 = gen env is_rec lecs in
           match uu____17215 with
           | FStar_Pervasives_Native.None ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____17314 ->
                       match uu____17314 with
                       | (l, t, c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____17376 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 if uu____17376
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____17424 ->
                           match uu____17424 with
                           | (l, us, e, c, gvs) ->
                               let uu____17458 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos in
                               let uu____17460 =
                                 FStar_Syntax_Print.lbname_to_string l in
                               let uu____17462 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c) in
                               let uu____17464 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____17466 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____17458 uu____17460 uu____17462
                                 uu____17464 uu____17466))
                 else ());
                luecs) in
         FStar_List.map2
           (fun univnames ->
              fun uu____17511 ->
                match uu____17511 with
                | (l, generalized_univs, t, c, gvs) ->
                    let uu____17555 =
                      check_universe_generalization univnames
                        generalized_univs t in
                    (l, uu____17555, t, c, gvs)) univnames_lecs
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
        let uu____17610 =
          let uu____17614 =
            let uu____17616 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.string_of_lid uu____17616 in
          FStar_Pervasives_Native.Some uu____17614 in
        FStar_Profiling.profile
          (fun uu____17633 -> generalize' env is_rec lecs) uu____17610
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
              let uu____17690 =
                FStar_TypeChecker_Rel.get_teq_predicate env2 t1 t21 in
              match uu____17690 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some f ->
                  let uu____17696 = FStar_TypeChecker_Env.apply_guard f e in
                  FStar_All.pipe_right uu____17696
                    (fun uu____17699 ->
                       FStar_Pervasives_Native.Some uu____17699)
            else
              if env2.FStar_TypeChecker_Env.use_eq
              then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
              else
                (let uu____17708 =
                   FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21 in
                 match uu____17708 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some f ->
                     let uu____17714 = FStar_TypeChecker_Env.apply_guard f e in
                     FStar_All.pipe_left
                       (fun uu____17717 ->
                          FStar_Pervasives_Native.Some uu____17717)
                       uu____17714) in
          let uu____17718 = maybe_coerce_lc env1 e lc t2 in
          match uu____17718 with
          | (e1, lc1, g_c) ->
              let uu____17734 =
                check env1 lc1.FStar_TypeChecker_Common.res_typ t2 in
              (match uu____17734 with
               | FStar_Pervasives_Native.None ->
                   let uu____17743 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ in
                   let uu____17749 = FStar_TypeChecker_Env.get_range env1 in
                   FStar_Errors.raise_error uu____17743 uu____17749
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____17758 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____17758
                     then
                       let uu____17763 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____17763
                     else ());
                    (let uu____17769 = FStar_TypeChecker_Env.conj_guard g g_c in
                     (e1, lc1, uu____17769))))
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env ->
    fun g ->
      fun lc ->
        (let uu____17797 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium in
         if uu____17797
         then
           let uu____17800 = FStar_TypeChecker_Common.lcomp_to_string lc in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____17800
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
         let uu____17814 = FStar_TypeChecker_Common.lcomp_comp lc in
         match uu____17814 with
         | (c, g_c) ->
             let uu____17826 = FStar_TypeChecker_Common.is_total_lcomp lc in
             if uu____17826
             then
               let uu____17834 =
                 let uu____17836 = FStar_TypeChecker_Env.conj_guard g1 g_c in
                 discharge uu____17836 in
               (uu____17834, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] in
                let c1 =
                  let uu____17844 =
                    let uu____17845 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    FStar_All.pipe_right uu____17845
                      FStar_Syntax_Syntax.mk_Comp in
                  FStar_All.pipe_right uu____17844
                    (FStar_TypeChecker_Normalize.normalize_comp steps env) in
                let uu____17846 = check_trivial_precondition env c1 in
                match uu____17846 with
                | (ct, vc, g_pre) ->
                    ((let uu____17862 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification") in
                      if uu____17862
                      then
                        let uu____17867 =
                          FStar_Syntax_Print.term_to_string vc in
                        FStar_Util.print1 "top-level VC: %s\n" uu____17867
                      else ());
                     (let uu____17872 =
                        let uu____17874 =
                          let uu____17875 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre in
                          FStar_TypeChecker_Env.conj_guard g1 uu____17875 in
                        discharge uu____17874 in
                      let uu____17876 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp in
                      (uu____17872, uu____17876)))))
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head ->
    fun seen_args ->
      let short_bin_op f uu___8_17910 =
        match uu___8_17910 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst, uu____17920)::[] -> f fst
        | uu____17945 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____17957 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____17957
          (fun uu____17958 -> FStar_TypeChecker_Common.NonTrivial uu____17958) in
      let op_or_e e =
        let uu____17969 =
          let uu____17970 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____17970 in
        FStar_All.pipe_right uu____17969
          (fun uu____17973 -> FStar_TypeChecker_Common.NonTrivial uu____17973) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun uu____17980 -> FStar_TypeChecker_Common.NonTrivial uu____17980) in
      let op_or_t t =
        let uu____17991 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____17991
          (fun uu____17994 -> FStar_TypeChecker_Common.NonTrivial uu____17994) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun uu____18001 -> FStar_TypeChecker_Common.NonTrivial uu____18001) in
      let short_op_ite uu___9_18007 =
        match uu___9_18007 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard, uu____18017)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard, uu____18044)::[] ->
            let uu____18085 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____18085
              (fun uu____18086 ->
                 FStar_TypeChecker_Common.NonTrivial uu____18086)
        | uu____18087 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____18099 =
          let uu____18107 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____18107) in
        let uu____18115 =
          let uu____18125 =
            let uu____18133 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____18133) in
          let uu____18141 =
            let uu____18151 =
              let uu____18159 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____18159) in
            let uu____18167 =
              let uu____18177 =
                let uu____18185 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____18185) in
              let uu____18193 =
                let uu____18203 =
                  let uu____18211 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____18211) in
                [uu____18203; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____18177 :: uu____18193 in
            uu____18151 :: uu____18167 in
          uu____18125 :: uu____18141 in
        uu____18099 :: uu____18115 in
      match head.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____18273 =
            FStar_Util.find_map table
              (fun uu____18288 ->
                 match uu____18288 with
                 | (x, mk) ->
                     let uu____18305 = FStar_Ident.lid_equals x lid in
                     if uu____18305
                     then
                       let uu____18310 = mk seen_args in
                       FStar_Pervasives_Native.Some uu____18310
                     else FStar_Pervasives_Native.None) in
          (match uu____18273 with
           | FStar_Pervasives_Native.None -> FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____18314 -> FStar_TypeChecker_Common.Trivial
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l ->
    let uu____18322 =
      let uu____18323 = FStar_Syntax_Util.un_uinst l in
      uu____18323.FStar_Syntax_Syntax.n in
    match uu____18322 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____18328 -> false
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env ->
    fun bs ->
      let pos bs1 =
        match bs1 with
        | (hd, uu____18364)::uu____18365 ->
            FStar_Syntax_Syntax.range_of_bv hd
        | uu____18384 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____18393, FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____18394))::uu____18395 -> bs
      | uu____18413 ->
          let uu____18414 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____18414 with
           | FStar_Pervasives_Native.None -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____18418 =
                 let uu____18419 = FStar_Syntax_Subst.compress t in
                 uu____18419.FStar_Syntax_Syntax.n in
               (match uu____18418 with
                | FStar_Syntax_Syntax.Tm_arrow (bs', uu____18423) ->
                    let uu____18444 =
                      FStar_Util.prefix_until
                        (fun uu___10_18484 ->
                           match uu___10_18484 with
                           | (uu____18492, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____18493)) ->
                               false
                           | uu____18498 -> true) bs' in
                    (match uu____18444 with
                     | FStar_Pervasives_Native.None -> bs
                     | FStar_Pervasives_Native.Some
                         ([], uu____18534, uu____18535) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps, uu____18607, uu____18608) ->
                         let uu____18681 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____18702 ->
                                   match uu____18702 with
                                   | (x, uu____18711) ->
                                       let uu____18716 =
                                         FStar_Ident.string_of_id
                                           x.FStar_Syntax_Syntax.ppname in
                                       FStar_Util.starts_with uu____18716 "'")) in
                         if uu____18681
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____18762 ->
                                     match uu____18762 with
                                     | (x, i) ->
                                         let uu____18781 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____18781, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____18792 -> bs))
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
            let uu____18821 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1)) in
            if uu____18821
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
          let uu____18852 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____18852
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
        (let uu____18895 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____18895
         then
           ((let uu____18900 = FStar_Ident.string_of_lid lident in
             d uu____18900);
            (let uu____18902 = FStar_Ident.string_of_lid lident in
             let uu____18904 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____18902 uu____18904))
         else ());
        (let fv =
           let uu____18910 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____18910
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
         let uu____18922 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Range.dummyRange in
         ((let uu___2156_18924 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2156_18924.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2156_18924.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2156_18924.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2156_18924.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2156_18924.FStar_Syntax_Syntax.sigopts)
           }), uu____18922))
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env ->
    fun se ->
      let visibility uu___11_18942 =
        match uu___11_18942 with
        | FStar_Syntax_Syntax.Private -> true
        | uu____18945 -> false in
      let reducibility uu___12_18953 =
        match uu___12_18953 with
        | FStar_Syntax_Syntax.Abstract -> true
        | FStar_Syntax_Syntax.Irreducible -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> true
        | FStar_Syntax_Syntax.Visible_default -> true
        | FStar_Syntax_Syntax.Inline_for_extraction -> true
        | uu____18960 -> false in
      let assumption uu___13_18968 =
        match uu___13_18968 with
        | FStar_Syntax_Syntax.Assumption -> true
        | FStar_Syntax_Syntax.New -> true
        | uu____18972 -> false in
      let reification uu___14_18980 =
        match uu___14_18980 with
        | FStar_Syntax_Syntax.Reifiable -> true
        | FStar_Syntax_Syntax.Reflectable uu____18983 -> true
        | uu____18985 -> false in
      let inferred uu___15_18993 =
        match uu___15_18993 with
        | FStar_Syntax_Syntax.Discriminator uu____18995 -> true
        | FStar_Syntax_Syntax.Projector uu____18997 -> true
        | FStar_Syntax_Syntax.RecordType uu____19003 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____19013 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor -> true
        | FStar_Syntax_Syntax.HasMaskedEffect -> true
        | FStar_Syntax_Syntax.Effect -> true
        | uu____19026 -> false in
      let has_eq uu___16_19034 =
        match uu___16_19034 with
        | FStar_Syntax_Syntax.Noeq -> true
        | FStar_Syntax_Syntax.Unopteq -> true
        | uu____19038 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____19117 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private -> true
        | uu____19124 -> true in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1 in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l ->
                  let uu____19157 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l in
                  FStar_Option.isSome uu____19157)) in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____19188 = FStar_Option.get attrs_opt in
                     FStar_Syntax_Util.has_attribute uu____19188
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
           | FStar_Syntax_Syntax.Sig_bundle uu____19208 ->
               let uu____19217 =
                 let uu____19219 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_19225 ->
                           match uu___17_19225 with
                           | FStar_Syntax_Syntax.Noeq -> true
                           | uu____19228 -> false)) in
                 Prims.op_Negation uu____19219 in
               if uu____19217
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____19235 -> ()
           | FStar_Syntax_Syntax.Sig_fail uu____19242 -> ()
           | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu____19256) ->
               let uu____19265 =
                 let uu____19267 =
                   FStar_TypeChecker_Env.non_informative env
                     lb.FStar_Syntax_Syntax.lbdef in
                 Prims.op_Negation uu____19267 in
               if uu____19265
               then
                 let uu____19270 =
                   let uu____19276 =
                     let uu____19278 =
                       FStar_Syntax_Print.term_to_string
                         lb.FStar_Syntax_Syntax.lbdef in
                     FStar_Util.format1
                       "Illegal attribute: the `erasable` attribute is only permitted on inductive type definitions and abbreviations for non-informative types. %s is considered informative."
                       uu____19278 in
                   (FStar_Errors.Fatal_QulifierListNotPermitted, uu____19276) in
                 FStar_Errors.raise_error uu____19270
                   (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.pos
               else ()
           | uu____19284 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_QulifierListNotPermitted,
                   "Illegal attribute: the `erasable` attribute is only permitted on inductive type definitions and abbreviations for non-informative types")
                 r)
        else () in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic))) in
      let uu____19298 =
        let uu____19300 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_19306 ->
                  match uu___18_19306 with
                  | FStar_Syntax_Syntax.OnlyName -> true
                  | uu____19309 -> false)) in
        FStar_All.pipe_right uu____19300 Prims.op_Negation in
      if uu____19298
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x -> fun y -> x = y) quals in
        let err' msg =
          let uu____19330 =
            let uu____19336 =
              let uu____19338 = FStar_Syntax_Print.quals_to_string quals in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____19338 msg in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____19336) in
          FStar_Errors.raise_error uu____19330 r in
        let err msg = err' (Prims.op_Hat ": " msg) in
        let err'1 uu____19356 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____19364 =
            let uu____19366 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____19366 in
          if uu____19364 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec, uu____19377), uu____19378)
              ->
              ((let uu____19390 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____19390
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____19399 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x -> (assumption x) || (has_eq x))) in
                if uu____19399
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____19410 ->
              ((let uu____19420 =
                  let uu____19422 =
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
                  Prims.op_Negation uu____19422 in
                if uu____19420 then err'1 () else ());
               (let uu____19432 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_19438 ->
                           match uu___19_19438 with
                           | FStar_Syntax_Syntax.Unopteq -> true
                           | uu____19441 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr) in
                if uu____19432
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____19447 ->
              let uu____19454 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____19454 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____19462 ->
              let uu____19469 =
                let uu____19471 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____19471 in
              if uu____19469 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____19481 ->
              let uu____19482 =
                let uu____19484 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____19484 in
              if uu____19482 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19494 ->
              let uu____19507 =
                let uu____19509 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____19509 in
              if uu____19507 then err'1 () else ()
          | uu____19519 -> ()))
      else ()
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g ->
    fun t ->
      let rec descend env t1 =
        let uu____19558 =
          let uu____19559 = FStar_Syntax_Subst.compress t1 in
          uu____19559.FStar_Syntax_Syntax.n in
        match uu____19558 with
        | FStar_Syntax_Syntax.Tm_arrow uu____19563 ->
            let uu____19578 = FStar_Syntax_Util.arrow_formals_comp t1 in
            (match uu____19578 with
             | (bs, c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____19587;
               FStar_Syntax_Syntax.index = uu____19588;
               FStar_Syntax_Syntax.sort = t2;_},
             uu____19590)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head, uu____19599) -> descend env head
        | FStar_Syntax_Syntax.Tm_uinst (head, uu____19625) ->
            descend env head
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____19631 -> false
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
        (let uu____19641 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction") in
         if uu____19641
         then
           let uu____19646 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____19646
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
                  let uu____19711 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t in
                  FStar_Errors.raise_error uu____19711 r in
                let uu____19721 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts in
                match uu____19721 with
                | (uu____19730, signature) ->
                    let uu____19732 =
                      let uu____19733 = FStar_Syntax_Subst.compress signature in
                      uu____19733.FStar_Syntax_Syntax.n in
                    (match uu____19732 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs, uu____19741) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____19789 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b ->
                                     let uu____19805 =
                                       FStar_Syntax_Print.binder_to_string b in
                                     let uu____19807 =
                                       FStar_Ident.string_of_lid eff_name in
                                     let uu____19809 =
                                       FStar_Range.string_of_range r in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____19805 uu____19807 uu____19809) r in
                              (match uu____19789 with
                               | (is, g) ->
                                   let uu____19822 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None ->
                                         let eff_c =
                                           let uu____19824 =
                                             let uu____19825 =
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
                                                 = uu____19825;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____19824 in
                                         let uu____19844 =
                                           let uu____19845 =
                                             let uu____19860 =
                                               let uu____19869 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   FStar_Syntax_Syntax.t_unit in
                                               [uu____19869] in
                                             (uu____19860, eff_c) in
                                           FStar_Syntax_Syntax.Tm_arrow
                                             uu____19845 in
                                         FStar_Syntax_Syntax.mk uu____19844 r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____19900 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u] in
                                           FStar_All.pipe_right uu____19900
                                             FStar_Pervasives_Native.snd in
                                         let uu____19909 =
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg (a_tm
                                             :: is) in
                                         FStar_Syntax_Syntax.mk_Tm_app repr
                                           uu____19909 r in
                                   (uu____19822, g))
                          | uu____19918 -> fail signature)
                     | uu____19919 -> fail signature)
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
            let uu____19950 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env) in
            FStar_All.pipe_right uu____19950
              (fun ed ->
                 let uu____19958 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____19958 u a_tm)
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
              let uu____19994 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u] in
              match uu____19994 with
              | (uu____19999, sig_tm) ->
                  let fail t =
                    let uu____20007 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t in
                    FStar_Errors.raise_error uu____20007 r in
                  let uu____20013 =
                    let uu____20014 = FStar_Syntax_Subst.compress sig_tm in
                    uu____20014.FStar_Syntax_Syntax.n in
                  (match uu____20013 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs, uu____20018) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs in
                       (match bs1 with
                        | (a', uu____20041)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____20063 -> fail sig_tm)
                   | uu____20064 -> fail sig_tm)
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
          (let uu____20095 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects") in
           if uu____20095
           then
             let uu____20100 = FStar_Syntax_Print.comp_to_string c in
             let uu____20102 = FStar_Syntax_Print.lid_to_string tgt in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____20100 uu____20102
           else ());
          (let r = FStar_TypeChecker_Env.get_range env in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c in
           let uu____20109 =
             let uu____20120 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs in
             let uu____20121 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst) in
             (uu____20120, (ct.FStar_Syntax_Syntax.result_typ), uu____20121) in
           match uu____20109 with
           | (u, a, c_is) ->
               let uu____20169 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u] in
               (match uu____20169 with
                | (uu____20178, lift_t) ->
                    let lift_t_shape_error s =
                      let uu____20189 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name in
                      let uu____20191 = FStar_Ident.string_of_lid tgt in
                      let uu____20193 =
                        FStar_Syntax_Print.term_to_string lift_t in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____20189 uu____20191 s uu____20193 in
                    let uu____20196 =
                      let uu____20229 =
                        let uu____20230 = FStar_Syntax_Subst.compress lift_t in
                        uu____20230.FStar_Syntax_Syntax.n in
                      match uu____20229 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs, c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____20294 =
                            FStar_Syntax_Subst.open_comp bs c1 in
                          (match uu____20294 with
                           | (a_b::bs1, c2) ->
                               let uu____20354 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one)) in
                               (a_b, uu____20354, c2))
                      | uu____20442 ->
                          let uu____20443 =
                            let uu____20449 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders" in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____20449) in
                          FStar_Errors.raise_error uu____20443 r in
                    (match uu____20196 with
                     | (a_b, (rest_bs, f_b::[]), lift_c) ->
                         let uu____20567 =
                           let uu____20574 =
                             let uu____20575 =
                               let uu____20576 =
                                 let uu____20583 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst in
                                 (uu____20583, a) in
                               FStar_Syntax_Syntax.NT uu____20576 in
                             [uu____20575] in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____20574
                             (fun b ->
                                let uu____20600 =
                                  FStar_Syntax_Print.binder_to_string b in
                                let uu____20602 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name in
                                let uu____20604 =
                                  FStar_Ident.string_of_lid tgt in
                                let uu____20606 =
                                  FStar_Range.string_of_range r in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____20600 uu____20602 uu____20604
                                  uu____20606) r in
                         (match uu____20567 with
                          | (rest_bs_uvars, g) ->
                              ((let uu____20620 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects") in
                                if uu____20620
                                then
                                  let uu____20625 =
                                    FStar_List.fold_left
                                      (fun s ->
                                         fun u1 ->
                                           let uu____20634 =
                                             let uu____20636 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1 in
                                             Prims.op_Hat ";;;;" uu____20636 in
                                           Prims.op_Hat s uu____20634) ""
                                      rest_bs_uvars in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____20625
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b ->
                                       fun t ->
                                         let uu____20667 =
                                           let uu____20674 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst in
                                           (uu____20674, t) in
                                         FStar_Syntax_Syntax.NT uu____20667)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars) in
                                let guard_f =
                                  let f_sort =
                                    let uu____20693 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs) in
                                    FStar_All.pipe_right uu____20693
                                      FStar_Syntax_Subst.compress in
                                  let f_sort_is =
                                    let uu____20699 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name in
                                    effect_args_from_repr f_sort uu____20699
                                      r in
                                  FStar_List.fold_left2
                                    (fun g1 ->
                                       fun i1 ->
                                         fun i2 ->
                                           let uu____20708 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2 in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____20708)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is in
                                let lift_ct =
                                  let uu____20710 =
                                    FStar_All.pipe_right lift_c
                                      (FStar_Syntax_Subst.subst_comp substs) in
                                  FStar_All.pipe_right uu____20710
                                    FStar_Syntax_Util.comp_to_comp_typ in
                                let is =
                                  let uu____20714 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____20714 r in
                                let fml =
                                  let uu____20719 =
                                    let uu____20724 =
                                      FStar_List.hd
                                        lift_ct.FStar_Syntax_Syntax.comp_univs in
                                    let uu____20725 =
                                      let uu____20726 =
                                        FStar_List.hd
                                          lift_ct.FStar_Syntax_Syntax.effect_args in
                                      FStar_Pervasives_Native.fst uu____20726 in
                                    (uu____20724, uu____20725) in
                                  match uu____20719 with
                                  | (u1, wp) ->
                                      FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                        env u1
                                        lift_ct.FStar_Syntax_Syntax.result_typ
                                        wp FStar_Range.dummyRange in
                                (let uu____20752 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects"))
                                     &&
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme) in
                                 if uu____20752
                                 then
                                   let uu____20758 =
                                     FStar_Syntax_Print.term_to_string fml in
                                   FStar_Util.print1 "Guard for lift is: %s"
                                     uu____20758
                                 else ());
                                (let c1 =
                                   let uu____20764 =
                                     let uu____20765 =
                                       FStar_All.pipe_right is
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.as_arg) in
                                     {
                                       FStar_Syntax_Syntax.comp_univs =
                                         (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                       FStar_Syntax_Syntax.effect_name = tgt;
                                       FStar_Syntax_Syntax.result_typ = a;
                                       FStar_Syntax_Syntax.effect_args =
                                         uu____20765;
                                       FStar_Syntax_Syntax.flags = []
                                     } in
                                   FStar_Syntax_Syntax.mk_Comp uu____20764 in
                                 (let uu____20789 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects") in
                                  if uu____20789
                                  then
                                    let uu____20794 =
                                      FStar_Syntax_Print.comp_to_string c1 in
                                    FStar_Util.print1 "} Lifted comp: %s\n"
                                      uu____20794
                                  else ());
                                 (let uu____20799 =
                                    let uu____20800 =
                                      FStar_TypeChecker_Env.conj_guard g
                                        guard_f in
                                    let uu____20801 =
                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                        (FStar_TypeChecker_Common.NonTrivial
                                           fml) in
                                    FStar_TypeChecker_Env.conj_guard
                                      uu____20800 uu____20801 in
                                  (c1, uu____20799)))))))))
let lift_tf_layered_effect_term :
  'uuuuuu20815 .
    'uuuuuu20815 ->
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
              let uu____20844 =
                let uu____20849 =
                  FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift
                    FStar_Util.must in
                FStar_All.pipe_right uu____20849
                  (fun ts -> FStar_TypeChecker_Env.inst_tscheme_with ts [u]) in
              FStar_All.pipe_right uu____20844 FStar_Pervasives_Native.snd in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must in
              let uu____20892 =
                let uu____20893 =
                  let uu____20896 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd in
                  FStar_All.pipe_right uu____20896
                    FStar_Syntax_Subst.compress in
                uu____20893.FStar_Syntax_Syntax.n in
              match uu____20892 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____20919::bs, uu____20921)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____20961 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one)) in
                  FStar_All.pipe_right uu____20961
                    FStar_Pervasives_Native.fst
              | uu____21067 ->
                  let uu____21068 =
                    let uu____21074 =
                      let uu____21076 =
                        FStar_Syntax_Print.tscheme_to_string lift_t in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____21076 in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____21074) in
                  FStar_Errors.raise_error uu____21068
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos in
            let args =
              let uu____21103 = FStar_Syntax_Syntax.as_arg a in
              let uu____21112 =
                let uu____21123 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____21159 ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const)) in
                let uu____21166 =
                  let uu____21177 = FStar_Syntax_Syntax.as_arg e in
                  [uu____21177] in
                FStar_List.append uu____21123 uu____21166 in
              uu____21103 :: uu____21112 in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              e.FStar_Syntax_Syntax.pos
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env ->
    fun datacon ->
      fun index ->
        let uu____21248 = FStar_TypeChecker_Env.lookup_datacon env datacon in
        match uu____21248 with
        | (uu____21253, t) ->
            let err n =
              let uu____21263 =
                let uu____21269 =
                  let uu____21271 = FStar_Ident.string_of_lid datacon in
                  let uu____21273 = FStar_Util.string_of_int n in
                  let uu____21275 = FStar_Util.string_of_int index in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____21271 uu____21273 uu____21275 in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____21269) in
              let uu____21279 = FStar_TypeChecker_Env.get_range env in
              FStar_Errors.raise_error uu____21263 uu____21279 in
            let uu____21280 =
              let uu____21281 = FStar_Syntax_Subst.compress t in
              uu____21281.FStar_Syntax_Syntax.n in
            (match uu____21280 with
             | FStar_Syntax_Syntax.Tm_arrow (bs, uu____21285) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____21340 ->
                           match uu____21340 with
                           | (uu____21348, q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true)) ->
                                    false
                                | uu____21357 -> true))) in
                 if (FStar_List.length bs1) <= index
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index in
                    FStar_Syntax_Util.mk_field_projector_name datacon
                      (FStar_Pervasives_Native.fst b) index)
             | uu____21391 -> err Prims.int_zero)
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env ->
    fun sub ->
      let uu____21404 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub.FStar_Syntax_Syntax.target) in
      if uu____21404
      then
        let uu____21407 =
          let uu____21420 =
            FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must in
          lift_tf_layered_effect sub.FStar_Syntax_Syntax.target uu____21420 in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____21407;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c in
           let uu____21455 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs in
           match uu____21455 with
           | (uu____21464, lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args in
               let uu____21483 =
                 let uu____21484 =
                   let uu___2540_21485 = ct in
                   let uu____21486 =
                     let uu____21497 =
                       let uu____21506 =
                         let uu____21507 =
                           let uu____21508 =
                             let uu____21525 =
                               let uu____21536 =
                                 FStar_Syntax_Syntax.as_arg
                                   ct.FStar_Syntax_Syntax.result_typ in
                               [uu____21536; wp] in
                             (lift_t, uu____21525) in
                           FStar_Syntax_Syntax.Tm_app uu____21508 in
                         FStar_Syntax_Syntax.mk uu____21507
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos in
                       FStar_All.pipe_right uu____21506
                         FStar_Syntax_Syntax.as_arg in
                     [uu____21497] in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2540_21485.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2540_21485.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____21486;
                     FStar_Syntax_Syntax.flags =
                       (uu___2540_21485.FStar_Syntax_Syntax.flags)
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____21484 in
               (uu____21483, FStar_TypeChecker_Common.trivial_guard) in
         let mk_mlift_term ts u r e =
           let uu____21636 = FStar_TypeChecker_Env.inst_tscheme_with ts [u] in
           match uu____21636 with
           | (uu____21643, lift_t) ->
               let uu____21645 =
                 let uu____21646 =
                   let uu____21663 =
                     let uu____21674 = FStar_Syntax_Syntax.as_arg r in
                     let uu____21683 =
                       let uu____21694 =
                         FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun in
                       let uu____21703 =
                         let uu____21714 = FStar_Syntax_Syntax.as_arg e in
                         [uu____21714] in
                       uu____21694 :: uu____21703 in
                     uu____21674 :: uu____21683 in
                   (lift_t, uu____21663) in
                 FStar_Syntax_Syntax.Tm_app uu____21646 in
               FStar_Syntax_Syntax.mk uu____21645 e.FStar_Syntax_Syntax.pos in
         let uu____21767 =
           let uu____21780 =
             FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must in
           FStar_All.pipe_right uu____21780 mk_mlift_wp in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____21767;
           FStar_TypeChecker_Env.mlift_term =
             (match sub.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____21816 ->
                        fun uu____21817 -> fun e -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env ->
    fun sub ->
      let uu____21840 = get_mlift_for_subeff env sub in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub.FStar_Syntax_Syntax.source sub.FStar_Syntax_Syntax.target
        uu____21840
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