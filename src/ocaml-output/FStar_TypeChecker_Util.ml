open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option *
    FStar_Syntax_Syntax.lcomp)
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
            FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t))
  =
  fun reason ->
    fun r ->
      fun env ->
        fun k ->
          FStar_TypeChecker_Env.new_implicit_var_aux reason r env k
            FStar_Syntax_Syntax.Strict FStar_Pervasives_Native.None
let (close_guard_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env ->
    fun xs ->
      fun g ->
        let uu____84 =
          let uu____86 = FStar_Options.eager_subtyping () in
          FStar_All.pipe_left Prims.op_Negation uu____86 in
        if uu____84
        then g
        else
          (let uu____93 =
             FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred
               (FStar_List.partition
                  (fun uu____145 ->
                     match uu____145 with
                     | (uu____152, p) ->
                         FStar_TypeChecker_Rel.flex_prob_closing env xs p)) in
           match uu____93 with
           | (solve_now, defer) ->
               ((let uu____187 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel") in
                 if uu____187
                 then
                   (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                    FStar_List.iter
                      (fun uu____204 ->
                         match uu____204 with
                         | (s, p) ->
                             let uu____214 =
                               FStar_TypeChecker_Rel.prob_to_string env p in
                             FStar_Util.print2 "%s: %s\n" s uu____214)
                      solve_now;
                    FStar_Util.print_string " ...DEFERRED THE REST:\n";
                    FStar_List.iter
                      (fun uu____229 ->
                         match uu____229 with
                         | (s, p) ->
                             let uu____239 =
                               FStar_TypeChecker_Rel.prob_to_string env p in
                             FStar_Util.print2 "%s: %s\n" s uu____239) defer;
                    FStar_Util.print_string "END\n")
                 else ());
                (let g1 =
                   FStar_TypeChecker_Rel.solve_deferred_constraints env
                     (let uu___46_247 = g in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          (uu___46_247.FStar_TypeChecker_Env.guard_f);
                        FStar_TypeChecker_Env.deferred = solve_now;
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___46_247.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___46_247.FStar_TypeChecker_Env.implicits)
                      }) in
                 let g2 =
                   let uu___49_249 = g1 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       (uu___49_249.FStar_TypeChecker_Env.guard_f);
                     FStar_TypeChecker_Env.deferred = defer;
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___49_249.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___49_249.FStar_TypeChecker_Env.implicits)
                   } in
                 g2)))
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r ->
    fun t ->
      let uvs = FStar_Syntax_Free.uvars t in
      let uu____264 =
        let uu____266 = FStar_Util.set_is_empty uvs in
        Prims.op_Negation uu____266 in
      if uu____264
      then
        let us =
          let uu____271 =
            let uu____275 = FStar_Util.set_elements uvs in
            FStar_List.map
              (fun u ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____275 in
          FStar_All.pipe_right uu____271 (FStar_String.concat ", ") in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____294 =
            let uu____300 =
              let uu____302 = FStar_Syntax_Print.term_to_string t in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____302 in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____300) in
          FStar_Errors.log_issue r uu____294);
         FStar_Options.pop ())
      else ()
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool))
  =
  fun env ->
    fun uu____325 ->
      match uu____325 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____336;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____338;
          FStar_Syntax_Syntax.lbpos = uu____339;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname in
          let t1 = FStar_Syntax_Subst.compress t in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown ->
               let uu____374 = FStar_Syntax_Subst.open_univ_vars univ_vars1 e in
               (match uu____374 with
                | (univ_vars2, e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2 in
                    let r = FStar_TypeChecker_Env.get_range env1 in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2 in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4, uu____412) -> aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4, t2, uu____419)
                          -> FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs, body, uu____474) ->
                          let res = aux body in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____510 = FStar_Options.ml_ish () in
                                if uu____510
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos in
                          ((let uu____532 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High in
                            if uu____532
                            then
                              let uu____535 = FStar_Range.string_of_range r in
                              let uu____537 =
                                FStar_Syntax_Print.term_to_string t2 in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____535 uu____537
                            else ());
                           FStar_Util.Inl t2)
                      | uu____542 -> FStar_Util.Inl FStar_Syntax_Syntax.tun in
                    let t2 =
                      let uu____544 = aux e1 in
                      match uu____544 with
                      | FStar_Util.Inr c ->
                          let uu____550 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c in
                          if uu____550
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____555 =
                               let uu____561 =
                                 let uu____563 =
                                   FStar_Syntax_Print.comp_to_string c in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____563 in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____561) in
                             FStar_Errors.raise_error uu____555 rng)
                      | FStar_Util.Inl t2 -> t2 in
                    (univ_vars2, t2, true))
           | uu____572 ->
               let uu____573 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1 in
               (match uu____573 with
                | (univ_vars2, t2) -> (univ_vars2, t2, false)))
let rec (decorated_pattern_as_term :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun pat ->
    let mk1 f =
      FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None
        pat.FStar_Syntax_Syntax.p in
    let pat_as_arg uu____637 =
      match uu____637 with
      | (p, i) ->
          let uu____657 = decorated_pattern_as_term p in
          (match uu____657 with
           | (vars, te) ->
               let uu____680 =
                 let uu____685 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____685) in
               (vars, uu____680)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____699 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____699)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____703 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____703)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____707 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____707)
    | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
        let uu____730 =
          let uu____749 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____749 FStar_List.unzip in
        (match uu____730 with
         | (vars, args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____887 =
               let uu____888 =
                 let uu____889 =
                   let uu____906 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____906, args) in
                 FStar_Syntax_Syntax.Tm_app uu____889 in
               mk1 uu____888 in
             (vars1, uu____887))
    | FStar_Syntax_Syntax.Pat_dot_term (x, e) -> ([], e)
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____945, uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____955, uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____969 -> FStar_Pervasives_Native.Some hd1)
let (lcomp_univ_opt :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun lc ->
    let uu____980 = FStar_All.pipe_right lc FStar_Syntax_Syntax.lcomp_comp in
    FStar_All.pipe_right uu____980 comp_univ_opt
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  =
  fun c ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp, uu____1009)::[] -> wp
      | uu____1034 ->
          let uu____1045 =
            let uu____1047 =
              let uu____1049 =
                FStar_List.map
                  (fun uu____1063 ->
                     match uu____1063 with
                     | (x, uu____1072) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____1049 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____1047 in
          failwith uu____1045 in
    let uu____1083 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____1083, (c.FStar_Syntax_Syntax.result_typ), wp)
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c ->
    fun m ->
      fun lift ->
        let uu____1100 = destruct_comp c in
        match uu____1100 with
        | (u, uu____1108, wp) ->
            let uu____1110 =
              let uu____1121 =
                let uu____1130 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____1130 in
              [uu____1121] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____1110;
              FStar_Syntax_Syntax.flags = []
            }
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env ->
    fun l1 ->
      fun l2 ->
        let uu____1163 =
          let uu____1170 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____1171 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____1170 uu____1171 in
        match uu____1163 with | (m, uu____1173, uu____1174) -> m
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env ->
    fun c1 ->
      fun c2 ->
        let uu____1191 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____1191
        then FStar_Parser_Const.effect_Tot_lid
        else
          join_effects env c1.FStar_Syntax_Syntax.eff_name
            c2.FStar_Syntax_Syntax.eff_name
let (lift_and_destruct :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv *
          FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.universe *
          FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) *
          (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
          FStar_Syntax_Syntax.typ)))
  =
  fun env ->
    fun c1 ->
      fun c2 ->
        let c11 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1 in
        let c21 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2 in
        let uu____1238 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____1238 with
        | (m, lift1, lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____1275 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____1275 with
             | (a, kwp) ->
                 let uu____1306 = destruct_comp m1 in
                 let uu____1313 = destruct_comp m2 in
                 ((md, a, kwp), uu____1306, uu____1313))
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
            let uu____1398 =
              let uu____1399 =
                let uu____1410 = FStar_Syntax_Syntax.as_arg wp in
                [uu____1410] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____1399;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____1398
let (mk_comp :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  = fun md -> mk_comp_l md.FStar_Syntax_Syntax.mname
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
          let uu____1494 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid in
          if uu____1494
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
let (subst_lcomp :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun subst1 ->
    fun lc ->
      let uu____1510 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____1510
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____1513 ->
           let uu____1514 = FStar_Syntax_Syntax.lcomp_comp lc in
           FStar_Syntax_Subst.subst_comp subst1 uu____1514)
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____1522 =
      let uu____1523 = FStar_Syntax_Subst.compress t in
      uu____1523.FStar_Syntax_Syntax.n in
    match uu____1522 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1527 -> true
    | uu____1543 -> false
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
          FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos
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
              let uu____1613 =
                let uu____1615 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____1615 in
              if uu____1613
              then f
              else (let uu____1622 = reason1 () in label uu____1622 r f)
let (label_guard :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun r ->
    fun reason ->
      fun g ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___243_1643 = g in
            let uu____1644 =
              let uu____1645 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____1645 in
            {
              FStar_TypeChecker_Env.guard_f = uu____1644;
              FStar_TypeChecker_Env.deferred =
                (uu___243_1643.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___243_1643.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___243_1643.FStar_TypeChecker_Env.implicits)
            }
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun bvs ->
      fun c ->
        let uu____1666 = FStar_Syntax_Util.is_ml_comp c in
        if uu____1666
        then c
        else
          (let uu____1671 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____1671
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x ->
                     fun wp ->
                       let bs =
                         let uu____1733 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____1733] in
                       let us =
                         let uu____1755 =
                           let uu____1758 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____1758] in
                         u_res :: uu____1755 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu____1764 =
                         let uu____1769 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____1770 =
                           let uu____1771 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____1780 =
                             let uu____1791 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____1800 =
                               let uu____1811 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____1811] in
                             uu____1791 :: uu____1800 in
                           uu____1771 :: uu____1780 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____1769 uu____1770 in
                       uu____1764 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____1853 = destruct_comp c1 in
              match uu____1853 with
              | (u_res_t, res_t, wp) ->
                  let md =
                    FStar_TypeChecker_Env.get_effect_decl env
                      c1.FStar_Syntax_Syntax.effect_name in
                  let wp1 = close_wp u_res_t md res_t bvs wp in
                  mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1
                    c1.FStar_Syntax_Syntax.flags))
let (close_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env ->
    fun bvs ->
      fun lc ->
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
          (fun uu____1889 ->
             let uu____1890 = FStar_Syntax_Syntax.lcomp_comp lc in
             close_comp env bvs uu____1890)
let (close_comp_if_refinement_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun t ->
      fun x ->
        fun c ->
          let t1 =
            FStar_TypeChecker_Normalize.normalize_refinement
              FStar_TypeChecker_Normalize.whnf_steps env t in
          match t1.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____1913;
                 FStar_Syntax_Syntax.index = uu____1914;
                 FStar_Syntax_Syntax.sort =
                   { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____1916;
                     FStar_Syntax_Syntax.vars = uu____1917;_};_},
               uu____1918)
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
              close_comp env [x] c
          | uu____1926 -> c
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___0_1938 ->
            match uu___0_1938 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> true
            | uu____1941 -> false))
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp -> Prims.bool)
  =
  fun env ->
    fun eopt ->
      fun lc ->
        let lc_is_unit_or_effectful =
          let uu____1966 =
            let uu____1969 =
              FStar_All.pipe_right lc.FStar_Syntax_Syntax.res_typ
                FStar_Syntax_Util.arrow_formals_comp in
            FStar_All.pipe_right uu____1969 FStar_Pervasives_Native.snd in
          FStar_All.pipe_right uu____1966
            (fun c ->
               (let uu____2025 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c in
                Prims.op_Negation uu____2025) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____2029 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c in
                     Prims.op_Negation uu____2029))) in
        match eopt with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____2040 = FStar_Syntax_Util.head_and_args' e in
                match uu____2040 with
                | (head1, uu____2057) ->
                    let uu____2078 =
                      let uu____2079 = FStar_Syntax_Util.un_uinst head1 in
                      uu____2079.FStar_Syntax_Syntax.n in
                    (match uu____2078 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2084 =
                           let uu____2086 = FStar_Syntax_Syntax.lid_of_fv fv in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____2086 in
                         Prims.op_Negation uu____2084
                     | uu____2087 -> true)))
              &&
              (let uu____2090 = should_not_inline_lc lc in
               Prims.op_Negation uu____2090)
let (return_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun u_t_opt ->
      fun t ->
        fun v1 ->
          let c =
            let uu____2118 =
              let uu____2120 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid in
              FStar_All.pipe_left Prims.op_Negation uu____2120 in
            if uu____2118
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____2127 = FStar_Syntax_Util.is_unit t in
               if uu____2127
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
                    let uu____2136 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____2136
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____2141 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid in
                       match uu____2141 with
                       | (a, kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp in
                           let uu____2151 =
                             let uu____2152 =
                               let uu____2157 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                               let uu____2158 =
                                 let uu____2159 =
                                   FStar_Syntax_Syntax.as_arg t in
                                 let uu____2168 =
                                   let uu____2179 =
                                     FStar_Syntax_Syntax.as_arg v1 in
                                   [uu____2179] in
                                 uu____2159 :: uu____2168 in
                               FStar_Syntax_Syntax.mk_Tm_app uu____2157
                                 uu____2158 in
                             uu____2152 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____2151) in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN])) in
          (let uu____2213 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return") in
           if uu____2213
           then
             let uu____2218 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
             let uu____2220 = FStar_Syntax_Print.term_to_string v1 in
             let uu____2222 =
               FStar_TypeChecker_Normalize.comp_to_string env c in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____2218 uu____2220 uu____2222
           else ());
          c
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags ->
    let uu____2239 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_2245 ->
              match uu___1_2245 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> true
              | uu____2248 -> false)) in
    if uu____2239
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_2260 ->
              match uu___2_2260 with
              | FStar_Syntax_Syntax.TOTAL ->
                  [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | FStar_Syntax_Syntax.RETURN ->
                  [FStar_Syntax_Syntax.PARTIAL_RETURN;
                  FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | f -> [f]))
let (weaken_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun c ->
      fun formula ->
        let uu____2280 = FStar_Syntax_Util.is_ml_comp c in
        if uu____2280
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
           let uu____2286 = destruct_comp c1 in
           match uu____2286 with
           | (u_res_t, res_t, wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name in
               let wp1 =
                 let uu____2300 =
                   let uu____2305 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p in
                   let uu____2306 =
                     let uu____2307 = FStar_Syntax_Syntax.as_arg res_t in
                     let uu____2316 =
                       let uu____2327 = FStar_Syntax_Syntax.as_arg formula in
                       let uu____2336 =
                         let uu____2347 = FStar_Syntax_Syntax.as_arg wp in
                         [uu____2347] in
                       uu____2327 :: uu____2336 in
                     uu____2307 :: uu____2316 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____2305 uu____2306 in
                 uu____2300 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos in
               let uu____2388 = weaken_flags c1.FStar_Syntax_Syntax.flags in
               mk_comp md u_res_t res_t wp1 uu____2388)
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env ->
    fun lc ->
      fun f ->
        let weaken uu____2412 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc in
          let uu____2414 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____2414
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1) in
        let uu____2420 = weaken_flags lc.FStar_Syntax_Syntax.cflags in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____2420 weaken
let (strengthen_comp :
  FStar_TypeChecker_Env.env ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.formula ->
          FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun reason ->
      fun c ->
        fun f ->
          fun flags ->
            if env.FStar_TypeChecker_Env.lax
            then c
            else
              (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
               let uu____2468 = destruct_comp c1 in
               match uu____2468 with
               | (u_res_t, res_t, wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name in
                   let wp1 =
                     let uu____2482 =
                       let uu____2487 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p in
                       let uu____2488 =
                         let uu____2489 = FStar_Syntax_Syntax.as_arg res_t in
                         let uu____2498 =
                           let uu____2509 =
                             let uu____2518 =
                               let uu____2519 =
                                 FStar_TypeChecker_Env.get_range env in
                               label_opt env reason uu____2519 f in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____2518 in
                           let uu____2528 =
                             let uu____2539 = FStar_Syntax_Syntax.as_arg wp in
                             [uu____2539] in
                           uu____2509 :: uu____2528 in
                         uu____2489 :: uu____2498 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____2487 uu____2488 in
                     uu____2482 FStar_Pervasives_Native.None
                       wp.FStar_Syntax_Syntax.pos in
                   mk_comp md u_res_t res_t wp1 flags)
let (strengthen_precondition :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_TypeChecker_Env.guard_t ->
            (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t))
  =
  fun reason ->
    fun env ->
      fun e_for_debugging_only ->
        fun lc ->
          fun g0 ->
            let uu____2625 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0 in
            if uu____2625
            then (lc, g0)
            else
              (let flags =
                 let uu____2637 =
                   let uu____2645 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
                   if uu____2645
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, []) in
                 match uu____2637 with
                 | (maybe_trivial_post, flags) ->
                     let uu____2675 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___3_2683 ->
                               match uu___3_2683 with
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
                               | uu____2686 -> [])) in
                     FStar_List.append flags uu____2675 in
               let strengthen uu____2692 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                    let uu____2698 = FStar_TypeChecker_Env.guard_form g01 in
                    match uu____2698 with
                    | FStar_TypeChecker_Common.Trivial -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____2701 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme in
                          if uu____2701
                          then
                            let uu____2705 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debugging_only in
                            let uu____2707 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____2705 uu____2707
                          else ());
                         strengthen_comp env reason c f flags)) in
               let uu____2712 =
                 let uu____2713 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name in
                 FStar_Syntax_Syntax.mk_lcomp uu____2713
                   lc.FStar_Syntax_Syntax.res_typ flags strengthen in
               (uu____2712,
                 (let uu___398_2715 = g0 in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___398_2715.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___398_2715.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___398_2715.FStar_TypeChecker_Env.implicits)
                  })))
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_2724 ->
            match uu___4_2724 with
            | FStar_Syntax_Syntax.SOMETRIVIAL -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION -> true
            | uu____2728 -> false) lc.FStar_Syntax_Syntax.cflags)
let (maybe_add_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env ->
    fun uopt ->
      fun lc ->
        fun e ->
          let uu____2757 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax in
          if uu____2757
          then e
          else
            (let uu____2764 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____2767 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid in
                  FStar_Option.isSome uu____2767) in
             if uu____2764
             then
               let u =
                 match uopt with
                 | FStar_Pervasives_Native.Some u -> u
                 | FStar_Pervasives_Native.None ->
                     env.FStar_TypeChecker_Env.universe_of env
                       lc.FStar_Syntax_Syntax.res_typ in
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
  fun r1 ->
    fun env ->
      fun e1opt ->
        fun lc1 ->
          fun uu____2820 ->
            match uu____2820 with
            | (b, lc2) ->
                let debug1 f =
                  let uu____2840 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____2840 then f () else () in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                let bind_flags =
                  let uu____2853 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21) in
                  if uu____2853
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____2863 = FStar_Syntax_Util.is_total_lcomp lc11 in
                       if uu____2863
                       then
                         let uu____2868 =
                           FStar_Syntax_Util.is_total_lcomp lc21 in
                         (if uu____2868
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____2875 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21 in
                             if uu____2875
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____2884 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21) in
                          if uu____2884
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else []) in
                     let uu____2891 = lcomp_has_trivial_postcondition lc21 in
                     if uu____2891
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags) in
                let bind_it uu____2903 =
                  let uu____2904 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ()) in
                  if uu____2904
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_Syntax_Syntax.res_typ in
                    lax_mk_tot_or_comp_l joined_eff u_t
                      lc21.FStar_Syntax_Syntax.res_typ []
                  else
                    (let c1 = FStar_Syntax_Syntax.lcomp_comp lc11 in
                     let c2 = FStar_Syntax_Syntax.lcomp_comp lc21 in
                     debug1
                       (fun uu____2921 ->
                          let uu____2922 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____2924 =
                            match b with
                            | FStar_Pervasives_Native.None -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x in
                          let uu____2929 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____2922 uu____2924 uu____2929);
                     (let aux uu____2947 =
                        let uu____2948 = FStar_Syntax_Util.is_trivial_wp c1 in
                        if uu____2948
                        then
                          match b with
                          | FStar_Pervasives_Native.None ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____2979 ->
                              let uu____2980 =
                                FStar_Syntax_Util.is_ml_comp c2 in
                              (if uu____2980
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____3012 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2) in
                           if uu____3012
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML") in
                      let try_simplify uu____3057 =
                        let uu____3058 =
                          let uu____3060 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid in
                          FStar_Option.isNone uu____3060 in
                        if uu____3058
                        then
                          let uu____3074 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                          (if uu____3074
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____3097 =
                                FStar_TypeChecker_Env.get_range env in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____3097))
                        else
                          (let uu____3112 =
                             FStar_Syntax_Util.is_total_comp c1 in
                           if uu____3112
                           then
                             let close1 x reason c =
                               let x1 =
                                 let uu___464_3154 = x in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___464_3154.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___464_3154.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (FStar_Syntax_Util.comp_result c1)
                                 } in
                               let uu____3155 =
                                 let uu____3161 =
                                   close_comp_if_refinement_t env
                                     x1.FStar_Syntax_Syntax.sort x1 c in
                                 (uu____3161, reason) in
                               FStar_Util.Inl uu____3155 in
                             match (e1opt, b) with
                             | (FStar_Pervasives_Native.Some e,
                                FStar_Pervasives_Native.Some x) ->
                                 let uu____3197 =
                                   FStar_All.pipe_right c2
                                     (FStar_Syntax_Subst.subst_comp
                                        [FStar_Syntax_Syntax.NT (x, e)]) in
                                 FStar_All.pipe_right uu____3197
                                   (close1 x "c1 Tot")
                             | (uu____3211, FStar_Pervasives_Native.Some x)
                                 ->
                                 FStar_All.pipe_right c2
                                   (close1 x "c1 Tot only close")
                             | (uu____3234, uu____3235) -> aux ()
                           else
                             (let uu____3250 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                              if uu____3250
                              then
                                let uu____3263 =
                                  let uu____3269 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2) in
                                  (uu____3269, "both GTot") in
                                FStar_Util.Inl uu____3263
                              else aux ())) in
                      let uu____3280 = try_simplify () in
                      match uu____3280 with
                      | FStar_Util.Inl (c, reason) ->
                          (debug1
                             (fun uu____3306 ->
                                let uu____3307 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____3307);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____3321 ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____3343 = lift_and_destruct env c11 c21 in
                              match uu____3343 with
                              | ((md, a, kwp), (u_t1, t1, wp1),
                                 (u_t2, t2, wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None ->
                                        let uu____3396 =
                                          FStar_Syntax_Syntax.null_binder t1 in
                                        [uu____3396]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____3416 =
                                          FStar_Syntax_Syntax.mk_binder x in
                                        [uu____3416] in
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
                                         (FStar_Const.Const_range r1))
                                      FStar_Pervasives_Native.None r1 in
                                  let wp_args =
                                    let uu____3463 =
                                      FStar_Syntax_Syntax.as_arg r11 in
                                    let uu____3472 =
                                      let uu____3483 =
                                        FStar_Syntax_Syntax.as_arg t1 in
                                      let uu____3492 =
                                        let uu____3503 =
                                          FStar_Syntax_Syntax.as_arg t2 in
                                        let uu____3512 =
                                          let uu____3523 =
                                            FStar_Syntax_Syntax.as_arg wp1 in
                                          let uu____3532 =
                                            let uu____3543 =
                                              let uu____3552 = mk_lam wp2 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____3552 in
                                            [uu____3543] in
                                          uu____3523 :: uu____3532 in
                                        uu____3503 :: uu____3512 in
                                      uu____3483 :: uu____3492 in
                                    uu____3463 :: uu____3472 in
                                  let wp =
                                    let uu____3604 =
                                      let uu____3609 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____3609 wp_args in
                                    uu____3604 FStar_Pervasives_Native.None
                                      t2.FStar_Syntax_Syntax.pos in
                                  mk_comp md u_t2 t2 wp bind_flags in
                            let mk_seq c11 b1 c21 =
                              let c12 =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c11 in
                              let c22 =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c21 in
                              let uu____3632 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name in
                              match uu____3632 with
                              | (m, uu____3640, lift2) ->
                                  let c23 =
                                    let uu____3643 = lift_comp c22 m lift2 in
                                    FStar_Syntax_Syntax.mk_Comp uu____3643 in
                                  let uu____3644 = destruct_comp c12 in
                                  (match uu____3644 with
                                   | (u1, t1, wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name in
                                       let vc1 =
                                         let uu____3658 =
                                           let uu____3663 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial in
                                           let uu____3664 =
                                             let uu____3665 =
                                               FStar_Syntax_Syntax.as_arg t1 in
                                             let uu____3674 =
                                               let uu____3685 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1 in
                                               [uu____3685] in
                                             uu____3665 :: uu____3674 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____3663 uu____3664 in
                                         uu____3658
                                           FStar_Pervasives_Native.None r1 in
                                       strengthen_comp env
                                         FStar_Pervasives_Native.None c23 vc1
                                         bind_flags) in
                            let c1_typ =
                              FStar_TypeChecker_Env.unfold_effect_abbrev env
                                c1 in
                            let uu____3723 = destruct_comp c1_typ in
                            match uu____3723 with
                            | (u_res_t1, res_t1, uu____3732) ->
                                let uu____3733 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11) in
                                if uu____3733
                                then
                                  let e1 = FStar_Option.get e1opt in
                                  let x = FStar_Option.get b in
                                  let uu____3738 =
                                    FStar_Syntax_Util.is_partial_return c1 in
                                  (if uu____3738
                                   then
                                     (debug1
                                        (fun uu____3748 ->
                                           let uu____3749 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1 in
                                           let uu____3751 =
                                             FStar_Syntax_Print.bv_to_string
                                               x in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____3749 uu____3751);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2 in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____3759 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____3762 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid in
                                           FStar_Option.isSome uu____3762) in
                                      if uu____3759
                                      then
                                        let e1' =
                                          let uu____3783 =
                                            FStar_Options.vcgen_decorate_with_type
                                              () in
                                          if uu____3783
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1 in
                                        (debug1
                                           (fun uu____3795 ->
                                              let uu____3796 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1' in
                                              let uu____3798 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____3796 uu____3798);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2 in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____3813 ->
                                              let uu____3814 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1 in
                                              let uu____3816 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____3814 uu____3816);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2 in
                                          let x_eq_e =
                                            let uu____3823 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____3823 in
                                          let c22 =
                                            weaken_comp env c21 x_eq_e in
                                          mk_bind c1 b c22))))
                                else mk_bind c1 b c2)))) in
                FStar_Syntax_Syntax.mk_lcomp joined_eff
                  lc21.FStar_Syntax_Syntax.res_typ bind_flags bind_it
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
      | uu____3841 -> g2
let (maybe_assume_result_eq_pure_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
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
            (let uu____3865 = FStar_Syntax_Util.is_lcomp_partial_return lc in
             Prims.op_Negation uu____3865) in
        let flags =
          if should_return1
          then
            let uu____3873 = FStar_Syntax_Util.is_total_lcomp lc in
            (if uu____3873
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____3889 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c) in
          let uu____3893 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
          if uu____3893
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e in
            let uu____3899 =
              let uu____3901 = FStar_Syntax_Util.is_pure_comp c in
              Prims.op_Negation uu____3901 in
            (if uu____3899
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
               let retc2 =
                 let uu___583_3908 = retc1 in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___583_3908.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___583_3908.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___583_3908.FStar_Syntax_Syntax.effect_args);
                   FStar_Syntax_Syntax.flags = flags
                 } in
               FStar_Syntax_Syntax.mk_Comp retc2
             else FStar_Syntax_Util.comp_set_flags retc flags)
          else
            (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
             let t = c1.FStar_Syntax_Syntax.result_typ in
             let c2 = FStar_Syntax_Syntax.mk_Comp c1 in
             let x =
               FStar_Syntax_Syntax.new_bv
                 (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t in
             let xexp = FStar_Syntax_Syntax.bv_to_name x in
             let ret1 =
               let uu____3921 =
                 let uu____3922 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp in
                 FStar_Syntax_Util.comp_set_flags uu____3922
                   [FStar_Syntax_Syntax.PARTIAL_RETURN] in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____3921 in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1) in
             let uu____3925 =
               let uu____3926 =
                 let uu____3927 = FStar_Syntax_Util.lcomp_of_comp c2 in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____3927
                   ((FStar_Pervasives_Native.Some x), eq_ret) in
               FStar_Syntax_Syntax.lcomp_comp uu____3926 in
             FStar_Syntax_Util.comp_set_flags uu____3925 flags) in
        if Prims.op_Negation should_return1
        then lc
        else
          FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
            lc.FStar_Syntax_Syntax.res_typ flags refine1
let (maybe_return_e2_and_bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_Syntax_Syntax.term ->
            lcomp_with_binder -> FStar_Syntax_Syntax.lcomp)
  =
  fun r ->
    fun env ->
      fun e1opt ->
        fun lc1 ->
          fun e2 ->
            fun uu____3965 ->
              match uu____3965 with
              | (x, lc2) ->
                  let lc21 =
                    let eff1 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc1.FStar_Syntax_Syntax.eff_name in
                    let eff2 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc2.FStar_Syntax_Syntax.eff_name in
                    let uu____3977 =
                      ((let uu____3981 = is_pure_or_ghost_effect env eff1 in
                        Prims.op_Negation uu____3981) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2) in
                    if uu____3977
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2 in
                  bind r env e1opt lc1 (x, lc21)
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun lid ->
      let uu____3999 =
        let uu____4000 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____4000 in
      FStar_Syntax_Syntax.fvar uu____3999 FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
let (bind_cases :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ * FStar_Ident.lident *
        FStar_Syntax_Syntax.cflag Prims.list *
        (Prims.bool -> FStar_Syntax_Syntax.lcomp)) Prims.list ->
        FStar_Syntax_Syntax.lcomp)
  =
  fun env ->
    fun res_t ->
      fun lcases ->
        let eff =
          FStar_List.fold_left
            (fun eff ->
               fun uu____4070 ->
                 match uu____4070 with
                 | (uu____4084, eff_label, uu____4086, uu____4087) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases in
        let uu____4100 =
          let uu____4108 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____4146 ->
                    match uu____4146 with
                    | (uu____4161, uu____4162, flags, uu____4164) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_4181 ->
                                match uu___5_4181 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE ->
                                    true
                                | uu____4184 -> false)))) in
          if uu____4108
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, []) in
        match uu____4100 with
        | (should_not_inline_whole_match, bind_cases_flags) ->
            let bind_cases uu____4217 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
              let uu____4219 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
              if uu____4219
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____4260 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos in
                   let uu____4261 =
                     let uu____4266 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else in
                     let uu____4267 =
                       let uu____4268 = FStar_Syntax_Syntax.as_arg res_t1 in
                       let uu____4277 =
                         let uu____4288 = FStar_Syntax_Syntax.as_arg g in
                         let uu____4297 =
                           let uu____4308 = FStar_Syntax_Syntax.as_arg wp_t in
                           let uu____4317 =
                             let uu____4328 = FStar_Syntax_Syntax.as_arg wp_e in
                             [uu____4328] in
                           uu____4308 :: uu____4317 in
                         uu____4288 :: uu____4297 in
                       uu____4268 :: uu____4277 in
                     FStar_Syntax_Syntax.mk_Tm_app uu____4266 uu____4267 in
                   uu____4261 FStar_Pervasives_Native.None uu____4260 in
                 let default_case =
                   let post_k =
                     let uu____4381 =
                       let uu____4390 = FStar_Syntax_Syntax.null_binder res_t in
                       [uu____4390] in
                     let uu____4409 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                     FStar_Syntax_Util.arrow uu____4381 uu____4409 in
                   let kwp =
                     let uu____4415 =
                       let uu____4424 =
                         FStar_Syntax_Syntax.null_binder post_k in
                       [uu____4424] in
                     let uu____4443 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                     FStar_Syntax_Util.arrow uu____4415 uu____4443 in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k in
                   let wp =
                     let uu____4450 =
                       let uu____4451 = FStar_Syntax_Syntax.mk_binder post in
                       [uu____4451] in
                     let uu____4470 =
                       let uu____4473 =
                         let uu____4480 = FStar_TypeChecker_Env.get_range env in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____4480 in
                       let uu____4481 =
                         fvar_const env FStar_Parser_Const.false_lid in
                       FStar_All.pipe_left uu____4473 uu____4481 in
                     FStar_Syntax_Util.abs uu____4450 uu____4470
                       (FStar_Pervasives_Native.Some
                          (FStar_Syntax_Util.mk_residual_comp
                             FStar_Parser_Const.effect_Tot_lid
                             FStar_Pervasives_Native.None
                             [FStar_Syntax_Syntax.TOTAL])) in
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       FStar_Parser_Const.effect_PURE_lid in
                   mk_comp md u_res_t res_t wp [] in
                 let maybe_return eff_label_then cthen =
                   let uu____4505 =
                     should_not_inline_whole_match ||
                       (let uu____4508 = is_pure_or_ghost_effect env eff in
                        Prims.op_Negation uu____4508) in
                   if uu____4505 then cthen true else cthen false in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____4547 ->
                        fun celse ->
                          match uu____4547 with
                          | (g, eff_label, uu____4564, cthen) ->
                              let uu____4578 =
                                let uu____4603 =
                                  let uu____4604 =
                                    maybe_return eff_label cthen in
                                  FStar_Syntax_Syntax.lcomp_comp uu____4604 in
                                lift_and_destruct env uu____4603 celse in
                              (match uu____4578 with
                               | ((md, uu____4606, uu____4607),
                                  (uu____4608, uu____4609, wp_then),
                                  (uu____4611, uu____4612, wp_else)) ->
                                   let uu____4632 =
                                     ifthenelse md res_t g wp_then wp_else in
                                   mk_comp md u_res_t res_t uu____4632 []))
                     lcases default_case in
                 match lcases with
                 | [] -> comp
                 | uu____4647::[] -> comp
                 | uu____4690 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name in
                     let uu____4709 = destruct_comp comp1 in
                     (match uu____4709 with
                      | (uu____4716, uu____4717, wp) ->
                          let wp1 =
                            let uu____4722 =
                              let uu____4727 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp in
                              let uu____4728 =
                                let uu____4729 =
                                  FStar_Syntax_Syntax.as_arg res_t in
                                let uu____4738 =
                                  let uu____4749 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____4749] in
                                uu____4729 :: uu____4738 in
                              FStar_Syntax_Syntax.mk_Tm_app uu____4727
                                uu____4728 in
                            uu____4722 FStar_Pervasives_Native.None
                              wp.FStar_Syntax_Syntax.pos in
                          mk_comp md u_res_t res_t wp1 bind_cases_flags)) in
            FStar_Syntax_Syntax.mk_lcomp eff res_t bind_cases_flags
              bind_cases
let (check_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
            FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun e ->
      fun c ->
        fun c' ->
          let uu____4815 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____4815 with
          | FStar_Pervasives_Native.None ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____4831 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c' in
                let uu____4837 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error uu____4831 uu____4837
              else
                (let uu____4846 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c' in
                 let uu____4852 = FStar_TypeChecker_Env.get_range env in
                 FStar_Errors.raise_error uu____4846 uu____4852)
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
          let uu____4877 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name in
          FStar_All.pipe_right uu____4877
            (FStar_TypeChecker_Env.norm_eff_name env) in
        let uu____4880 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid in
        if uu____4880
        then u_res
        else
          (let is_total =
             let uu____4887 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid in
             FStar_All.pipe_right uu____4887
               (FStar_List.existsb
                  (fun q -> q = FStar_Syntax_Syntax.TotalEffect)) in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____4898 = FStar_TypeChecker_Env.effect_repr env c u_res in
              match uu____4898 with
              | FStar_Pervasives_Native.None ->
                  let uu____4901 =
                    let uu____4907 =
                      let uu____4909 = FStar_Syntax_Print.lid_to_string c_lid in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____4909 in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____4907) in
                  FStar_Errors.raise_error uu____4901
                    c.FStar_Syntax_Syntax.pos
              | FStar_Pervasives_Native.Some tm ->
                  env.FStar_TypeChecker_Env.universe_of env tm))
let (maybe_coerce_bool_to_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp))
  =
  fun env ->
    fun e ->
      fun lc ->
        fun t ->
          if env.FStar_TypeChecker_Env.is_pattern
          then (e, lc)
          else
            (let is_type1 t1 =
               let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1 in
               let uu____4954 =
                 let uu____4955 = FStar_Syntax_Subst.compress t2 in
                 uu____4955.FStar_Syntax_Syntax.n in
               match uu____4954 with
               | FStar_Syntax_Syntax.Tm_type uu____4959 -> true
               | uu____4961 -> false in
             let uu____4963 =
               let uu____4964 =
                 FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ in
               uu____4964.FStar_Syntax_Syntax.n in
             match uu____4963 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____4972 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid in
                 let b2t1 =
                   let uu____4982 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos in
                   FStar_Syntax_Syntax.fvar uu____4982
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        (Prims.parse_int "1")) FStar_Pervasives_Native.None in
                 let lc1 =
                   let uu____4985 =
                     let uu____4986 =
                       let uu____4987 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0 in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____4987 in
                     (FStar_Pervasives_Native.None, uu____4986) in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____4985 in
                 let e1 =
                   let uu____4993 =
                     let uu____4998 =
                       let uu____4999 = FStar_Syntax_Syntax.as_arg e in
                       [uu____4999] in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4998 in
                   uu____4993 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos in
                 (e1, lc1)
             | uu____5024 -> (e, lc))
let (weaken_result_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
            FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun e ->
      fun lc ->
        fun t ->
          (let uu____5059 =
             FStar_TypeChecker_Env.debug env FStar_Options.High in
           if uu____5059
           then
             let uu____5062 = FStar_Syntax_Print.term_to_string e in
             let uu____5064 = FStar_Syntax_Print.lcomp_to_string lc in
             let uu____5066 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____5062 uu____5064 uu____5066
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____5076 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_Syntax_Syntax.eff_name in
                match uu____5076 with
                | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____5101 -> false) in
           let gopt =
             if use_eq
             then
               let uu____5127 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____5127, false)
             else
               (let uu____5137 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_Syntax_Syntax.res_typ t in
                (uu____5137, true)) in
           match gopt with
           | (FStar_Pervasives_Native.None, uu____5150) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____5162 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_Syntax_Syntax.res_typ in
                 FStar_Errors.raise_error uu____5162
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_Syntax_Syntax.res_typ t;
                  (e,
                    ((let uu___739_5178 = lc in
                      {
                        FStar_Syntax_Syntax.eff_name =
                          (uu___739_5178.FStar_Syntax_Syntax.eff_name);
                        FStar_Syntax_Syntax.res_typ = t;
                        FStar_Syntax_Syntax.cflags =
                          (uu___739_5178.FStar_Syntax_Syntax.cflags);
                        FStar_Syntax_Syntax.comp_thunk =
                          (uu___739_5178.FStar_Syntax_Syntax.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g, apply_guard1) ->
               let uu____5185 = FStar_TypeChecker_Env.guard_form g in
               (match uu____5185 with
                | FStar_TypeChecker_Common.Trivial ->
                    let strengthen_trivial uu____5197 =
                      let c = FStar_Syntax_Syntax.lcomp_comp lc in
                      let res_t = FStar_Syntax_Util.comp_result c in
                      let set_result_typ1 c1 =
                        FStar_Syntax_Util.set_result_typ c1 t in
                      let uu____5208 =
                        let uu____5210 = FStar_Syntax_Util.eq_tm t res_t in
                        uu____5210 = FStar_Syntax_Util.Equal in
                      if uu____5208
                      then
                        ((let uu____5213 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme in
                          if uu____5213
                          then
                            let uu____5217 =
                              FStar_Syntax_Print.term_to_string res_t in
                            let uu____5219 =
                              FStar_Syntax_Print.term_to_string t in
                            FStar_Util.print2
                              "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                              uu____5217 uu____5219
                          else ());
                         set_result_typ1 c)
                      else
                        (let is_res_t_refinement =
                           let res_t1 =
                             FStar_TypeChecker_Normalize.normalize_refinement
                               FStar_TypeChecker_Normalize.whnf_steps env
                               res_t in
                           match res_t1.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_refine uu____5230 -> true
                           | uu____5238 -> false in
                         if is_res_t_refinement
                         then
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (res_t.FStar_Syntax_Syntax.pos)) res_t in
                           let cret =
                             let uu____5243 =
                               FStar_Syntax_Syntax.bv_to_name x in
                             return_value env (comp_univ_opt c) res_t
                               uu____5243 in
                           let lc1 =
                             let uu____5245 =
                               FStar_Syntax_Util.lcomp_of_comp c in
                             let uu____5246 =
                               let uu____5247 =
                                 FStar_Syntax_Util.lcomp_of_comp cret in
                               ((FStar_Pervasives_Native.Some x), uu____5247) in
                             bind e.FStar_Syntax_Syntax.pos env
                               (FStar_Pervasives_Native.Some e) uu____5245
                               uu____5246 in
                           ((let uu____5251 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme in
                             if uu____5251
                             then
                               let uu____5255 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____5257 =
                                 FStar_Syntax_Print.comp_to_string c in
                               let uu____5259 =
                                 FStar_Syntax_Print.term_to_string t in
                               let uu____5261 =
                                 FStar_Syntax_Print.lcomp_to_string lc1 in
                               FStar_Util.print4
                                 "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                 uu____5255 uu____5257 uu____5259 uu____5261
                             else ());
                            (let uu____5266 =
                               FStar_Syntax_Syntax.lcomp_comp lc1 in
                             set_result_typ1 uu____5266))
                         else
                           ((let uu____5270 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme in
                             if uu____5270
                             then
                               let uu____5274 =
                                 FStar_Syntax_Print.term_to_string res_t in
                               let uu____5276 =
                                 FStar_Syntax_Print.comp_to_string c in
                               FStar_Util.print2
                                 "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                 uu____5274 uu____5276
                             else ());
                            set_result_typ1 c)) in
                    let lc1 =
                      FStar_Syntax_Syntax.mk_lcomp
                        lc.FStar_Syntax_Syntax.eff_name t
                        lc.FStar_Syntax_Syntax.cflags strengthen_trivial in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___771_5284 = g in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___771_5284.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___771_5284.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___771_5284.FStar_TypeChecker_Env.implicits)
                      } in
                    let strengthen uu____5290 =
                      let uu____5291 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ()) in
                      if uu____5291
                      then FStar_Syntax_Syntax.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f in
                         let uu____5297 =
                           let uu____5298 = FStar_Syntax_Subst.compress f1 in
                           uu____5298.FStar_Syntax_Syntax.n in
                         match uu____5297 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____5301,
                              {
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Tm_fvar fv;
                                FStar_Syntax_Syntax.pos = uu____5303;
                                FStar_Syntax_Syntax.vars = uu____5304;_},
                              uu____5305)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___787_5331 = lc in
                               {
                                 FStar_Syntax_Syntax.eff_name =
                                   (uu___787_5331.FStar_Syntax_Syntax.eff_name);
                                 FStar_Syntax_Syntax.res_typ = t;
                                 FStar_Syntax_Syntax.cflags =
                                   (uu___787_5331.FStar_Syntax_Syntax.cflags);
                                 FStar_Syntax_Syntax.comp_thunk =
                                   (uu___787_5331.FStar_Syntax_Syntax.comp_thunk)
                               } in
                             FStar_Syntax_Syntax.lcomp_comp lc1
                         | uu____5332 ->
                             let c = FStar_Syntax_Syntax.lcomp_comp lc in
                             ((let uu____5335 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   FStar_Options.Extreme in
                               if uu____5335
                               then
                                 let uu____5339 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env lc.FStar_Syntax_Syntax.res_typ in
                                 let uu____5341 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env t in
                                 let uu____5343 =
                                   FStar_TypeChecker_Normalize.comp_to_string
                                     env c in
                                 let uu____5345 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env f1 in
                                 FStar_Util.print4
                                   "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                   uu____5339 uu____5341 uu____5343
                                   uu____5345
                               else ());
                              (let u_t_opt = comp_univ_opt c in
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (t.FStar_Syntax_Syntax.pos)) t in
                               let xexp = FStar_Syntax_Syntax.bv_to_name x in
                               let cret = return_value env u_t_opt t xexp in
                               let guard =
                                 if apply_guard1
                                 then
                                   let uu____5358 =
                                     let uu____5363 =
                                       let uu____5364 =
                                         FStar_Syntax_Syntax.as_arg xexp in
                                       [uu____5364] in
                                     FStar_Syntax_Syntax.mk_Tm_app f1
                                       uu____5363 in
                                   uu____5358 FStar_Pervasives_Native.None
                                     f1.FStar_Syntax_Syntax.pos
                                 else f1 in
                               let uu____5391 =
                                 let uu____5396 =
                                   FStar_All.pipe_left
                                     (fun _5417 ->
                                        FStar_Pervasives_Native.Some _5417)
                                     (FStar_TypeChecker_Err.subtyping_failed
                                        env lc.FStar_Syntax_Syntax.res_typ t) in
                                 let uu____5418 =
                                   FStar_TypeChecker_Env.set_range env
                                     e.FStar_Syntax_Syntax.pos in
                                 let uu____5419 =
                                   FStar_Syntax_Util.lcomp_of_comp cret in
                                 let uu____5420 =
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                     (FStar_TypeChecker_Common.NonTrivial
                                        guard) in
                                 strengthen_precondition uu____5396
                                   uu____5418 e uu____5419 uu____5420 in
                               match uu____5391 with
                               | (eq_ret, _trivial_so_ok_to_discard) ->
                                   let x1 =
                                     let uu___803_5424 = x in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         (uu___803_5424.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (uu___803_5424.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (lc.FStar_Syntax_Syntax.res_typ)
                                     } in
                                   let c1 =
                                     let uu____5426 =
                                       FStar_Syntax_Util.lcomp_of_comp c in
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (FStar_Pervasives_Native.Some e)
                                       uu____5426
                                       ((FStar_Pervasives_Native.Some x1),
                                         eq_ret) in
                                   let c2 = FStar_Syntax_Syntax.lcomp_comp c1 in
                                   ((let uu____5431 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme in
                                     if uu____5431
                                     then
                                       let uu____5435 =
                                         FStar_TypeChecker_Normalize.comp_to_string
                                           env c2 in
                                       FStar_Util.print1
                                         "Strengthened to %s\n" uu____5435
                                     else ());
                                    c2)))) in
                    let flags =
                      FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                        (FStar_List.collect
                           (fun uu___6_5448 ->
                              match uu___6_5448 with
                              | FStar_Syntax_Syntax.RETURN ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____5451 -> [])) in
                    let lc1 =
                      let uu____5453 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_Syntax_Syntax.eff_name in
                      FStar_Syntax_Syntax.mk_lcomp uu____5453 t flags
                        strengthen in
                    let g2 =
                      let uu___817_5455 = g1 in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___817_5455.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___817_5455.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___817_5455.FStar_TypeChecker_Env.implicits)
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
        let uu____5491 =
          let uu____5494 =
            let uu____5499 =
              let uu____5500 =
                let uu____5509 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____5509 in
              [uu____5500] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____5499 in
          uu____5494 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____5491 in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t in
      let uu____5532 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____5532
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____5551 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____5567 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____5584 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid) in
             if uu____5584
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req, uu____5600)::(ens, uu____5602)::uu____5603 ->
                    let uu____5646 =
                      let uu____5649 = norm1 req in
                      FStar_Pervasives_Native.Some uu____5649 in
                    let uu____5650 =
                      let uu____5651 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm1 uu____5651 in
                    (uu____5646, uu____5650)
                | uu____5654 ->
                    let uu____5665 =
                      let uu____5671 =
                        let uu____5673 =
                          FStar_Syntax_Print.comp_to_string comp in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____5673 in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____5671) in
                    FStar_Errors.raise_error uu____5665
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp, uu____5693)::uu____5694 ->
                    let uu____5721 =
                      let uu____5726 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____5726 in
                    (match uu____5721 with
                     | (us_r, uu____5758) ->
                         let uu____5759 =
                           let uu____5764 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____5764 in
                         (match uu____5759 with
                          | (us_e, uu____5796) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____5799 =
                                  let uu____5800 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r in
                                  FStar_Syntax_Syntax.fvar uu____5800
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____5799
                                  us_r in
                              let as_ens =
                                let uu____5802 =
                                  let uu____5803 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r in
                                  FStar_Syntax_Syntax.fvar uu____5803
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____5802
                                  us_e in
                              let req =
                                let uu____5807 =
                                  let uu____5812 =
                                    let uu____5813 =
                                      let uu____5824 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____5824] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____5813 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____5812 in
                                uu____5807 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____5864 =
                                  let uu____5869 =
                                    let uu____5870 =
                                      let uu____5881 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____5881] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____5870 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____5869 in
                                uu____5864 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____5918 =
                                let uu____5921 = norm1 req in
                                FStar_Pervasives_Native.Some uu____5921 in
                              let uu____5922 =
                                let uu____5923 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm1 uu____5923 in
                              (uu____5918, uu____5922)))
                | uu____5926 -> failwith "Impossible"))
let (reify_body :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let tm = FStar_Syntax_Util.mk_reify t in
      let tm' =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Reify;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses] env tm in
      (let uu____5960 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____5960
       then
         let uu____5965 = FStar_Syntax_Print.term_to_string tm in
         let uu____5967 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____5965 uu____5967
       else ());
      tm'
let (reify_body_with_arg :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.arg -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun head1 ->
      fun arg ->
        let tm =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (head1, [arg]))
            FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos in
        let tm' =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Eager_unfolding;
            FStar_TypeChecker_Env.EraseUniverses;
            FStar_TypeChecker_Env.AllowUnboundUniverses] env tm in
        (let uu____6021 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____6021
         then
           let uu____6026 = FStar_Syntax_Print.term_to_string tm in
           let uu____6028 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6026
             uu____6028
         else ());
        tm'
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____6039 =
      let uu____6041 =
        let uu____6042 = FStar_Syntax_Subst.compress t in
        uu____6042.FStar_Syntax_Syntax.n in
      match uu____6041 with
      | FStar_Syntax_Syntax.Tm_app uu____6046 -> false
      | uu____6064 -> true in
    if uu____6039
    then t
    else
      (let uu____6069 = FStar_Syntax_Util.head_and_args t in
       match uu____6069 with
       | (head1, args) ->
           let uu____6112 =
             let uu____6114 =
               let uu____6115 = FStar_Syntax_Subst.compress head1 in
               uu____6115.FStar_Syntax_Syntax.n in
             match uu____6114 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) ->
                 true
             | uu____6120 -> false in
           if uu____6112
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____6152 ->
                  failwith
                    "Impossible : Reify applied to multiple arguments after normalization.")
           else t)
let (maybe_instantiate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
          FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun e ->
      fun t ->
        let torig = FStar_Syntax_Subst.compress t in
        if Prims.op_Negation env.FStar_TypeChecker_Env.instantiate_imp
        then (e, torig, FStar_TypeChecker_Env.trivial_guard)
        else
          ((let uu____6199 =
              FStar_TypeChecker_Env.debug env FStar_Options.High in
            if uu____6199
            then
              let uu____6202 = FStar_Syntax_Print.term_to_string e in
              let uu____6204 = FStar_Syntax_Print.term_to_string t in
              let uu____6206 =
                let uu____6208 = FStar_TypeChecker_Env.expected_typ env in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____6208 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____6202 uu____6204 uu____6206
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1 in
              let uu____6221 = FStar_Syntax_Util.arrow_formals t2 in
              match uu____6221 with
              | (formals, uu____6237) ->
                  let n_implicits =
                    let uu____6259 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____6337 ->
                              match uu____6337 with
                              | (uu____6345, imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____6352 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality) in
                                     uu____6352 = FStar_Syntax_Util.Equal))) in
                    match uu____6259 with
                    | FStar_Pervasives_Native.None ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits, _first_explicit, _rest) ->
                        FStar_List.length implicits in
                  n_implicits in
            let inst_n_binders t1 =
              let uu____6477 = FStar_TypeChecker_Env.expected_typ env in
              match uu____6477 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t in
                  let n_available = number_of_implicits t1 in
                  if n_available < n_expected
                  then
                    let uu____6491 =
                      let uu____6497 =
                        let uu____6499 = FStar_Util.string_of_int n_expected in
                        let uu____6501 = FStar_Syntax_Print.term_to_string e in
                        let uu____6503 = FStar_Util.string_of_int n_available in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____6499 uu____6501 uu____6503 in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____6497) in
                    let uu____6507 = FStar_TypeChecker_Env.get_range env in
                    FStar_Errors.raise_error uu____6491 uu____6507
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected) in
            let decr_inst uu___7_6525 =
              match uu___7_6525 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                let uu____6568 = FStar_Syntax_Subst.open_comp bs c in
                (match uu____6568 with
                 | (bs1, c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _6699, uu____6686)
                           when _6699 = (Prims.parse_int "0") ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____6732,
                          (x, FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit uu____6734))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort in
                           let uu____6768 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2 in
                           (match uu____6768 with
                            | (v1, uu____6809, g) ->
                                ((let uu____6824 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High in
                                  if uu____6824
                                  then
                                    let uu____6827 =
                                      FStar_Syntax_Print.term_to_string v1 in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____6827
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1 in
                                  let uu____6837 =
                                    aux subst2 (decr_inst inst_n) rest in
                                  match uu____6837 with
                                  | (args, bs3, subst3, g') ->
                                      let uu____6930 =
                                        FStar_TypeChecker_Env.conj_guard g g' in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____6930))))
                       | (uu____6957,
                          (x, FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tau))::rest) ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort in
                           let uu____6994 =
                             let uu____7007 =
                               let uu____7014 =
                                 let uu____7019 = FStar_Dyn.mkdyn env in
                                 (uu____7019, tau) in
                               FStar_Pervasives_Native.Some uu____7014 in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____7007 in
                           (match uu____6994 with
                            | (v1, uu____7052, g) ->
                                ((let uu____7067 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High in
                                  if uu____7067
                                  then
                                    let uu____7070 =
                                      FStar_Syntax_Print.term_to_string v1 in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____7070
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1 in
                                  let uu____7080 =
                                    aux subst2 (decr_inst inst_n) rest in
                                  match uu____7080 with
                                  | (args, bs3, subst3, g') ->
                                      let uu____7173 =
                                        FStar_TypeChecker_Env.conj_guard g g' in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____7173))))
                       | (uu____7200, bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard) in
                     let uu____7248 =
                       let uu____7275 = inst_n_binders t1 in
                       aux [] uu____7275 bs1 in
                     (match uu____7248 with
                      | (args, bs2, subst1, guard) ->
                          (match (args, bs2) with
                           | ([], uu____7347) -> (e, torig, guard)
                           | (uu____7378, []) when
                               let uu____7409 =
                                 FStar_Syntax_Util.is_total_comp c1 in
                               Prims.op_Negation uu____7409 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____7411 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____7439 ->
                                     FStar_Syntax_Util.arrow bs2 c1 in
                               let t3 = FStar_Syntax_Subst.subst subst1 t2 in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   FStar_Pervasives_Native.None
                                   e.FStar_Syntax_Syntax.pos in
                               (e1, t3, guard))))
            | uu____7452 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1 ->
    let uu____7464 =
      let uu____7468 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____7468
        (FStar_List.map
           (fun u ->
              let uu____7480 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____7480 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____7464 (FStar_String.concat ", ")
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env ->
    fun x ->
      let uu____7508 = FStar_Util.set_is_empty x in
      if uu____7508
      then []
      else
        (let s =
           let uu____7526 =
             let uu____7529 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____7529 in
           FStar_All.pipe_right uu____7526 FStar_Util.set_elements in
         (let uu____7545 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____7545
          then
            let uu____7550 =
              let uu____7552 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____7552 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____7550
          else ());
         (let r =
            let uu____7561 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____7561 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____7600 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____7600
                     then
                       let uu____7605 =
                         let uu____7607 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____7607 in
                       let uu____7611 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____7613 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____7605 uu____7611 uu____7613
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
      let univnames1 =
        let uu____7643 = FStar_Util.set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____7643 FStar_Util.set_elements in
      univnames1
let (check_universe_generalization :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun explicit_univ_names ->
    fun generalized_univ_names ->
      fun t ->
        match (explicit_univ_names, generalized_univ_names) with
        | ([], uu____7682) -> generalized_univ_names
        | (uu____7689, []) -> explicit_univ_names
        | uu____7696 ->
            let uu____7705 =
              let uu____7711 =
                let uu____7713 = FStar_Syntax_Print.term_to_string t in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____7713 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____7711) in
            FStar_Errors.raise_error uu____7705 t.FStar_Syntax_Syntax.pos
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
      let univnames1 = gather_free_univnames env t in
      (let uu____7735 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____7735
       then
         let uu____7740 = FStar_Syntax_Print.term_to_string t in
         let uu____7742 = FStar_Syntax_Print.univ_names_to_string univnames1 in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____7740 uu____7742
       else ());
      (let univs1 = FStar_Syntax_Free.univs t in
       (let uu____7751 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____7751
        then
          let uu____7756 = string_of_univs univs1 in
          FStar_Util.print1 "univs to gen : %s\n" uu____7756
        else ());
       (let gen1 = gen_univs env univs1 in
        (let uu____7765 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen") in
         if uu____7765
         then
           let uu____7770 = FStar_Syntax_Print.term_to_string t in
           let uu____7772 = FStar_Syntax_Print.univ_names_to_string gen1 in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____7770 uu____7772
         else ());
        (let univs2 = check_universe_generalization univnames1 gen1 t0 in
         let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t in
         let ts = FStar_Syntax_Subst.close_univ_vars univs2 t1 in
         (univs2, ts))))
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
        let uu____7856 =
          let uu____7858 =
            FStar_Util.for_all
              (fun uu____7872 ->
                 match uu____7872 with
                 | (uu____7882, uu____7883, c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          FStar_All.pipe_left Prims.op_Negation uu____7858 in
        if uu____7856
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____7935 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              if uu____7935
              then
                let uu____7938 = FStar_Syntax_Print.comp_to_string c in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____7938
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c in
              (let uu____7945 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____7945
               then
                 let uu____7948 = FStar_Syntax_Print.comp_to_string c1 in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____7948
               else ());
              c1) in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu____7966 = FStar_Util.set_difference uvs env_uvars in
             FStar_All.pipe_right uu____7966 FStar_Util.set_elements in
           let univs_and_uvars_of_lec uu____8000 =
             match uu____8000 with
             | (lbname, e, c) ->
                 let c1 = norm1 c in
                 let t = FStar_Syntax_Util.comp_result c1 in
                 let univs1 = FStar_Syntax_Free.univs t in
                 let uvt = FStar_Syntax_Free.uvars t in
                 ((let uu____8037 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen") in
                   if uu____8037
                   then
                     let uu____8042 =
                       let uu____8044 =
                         let uu____8048 = FStar_Util.set_elements univs1 in
                         FStar_All.pipe_right uu____8048
                           (FStar_List.map
                              (fun u ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u))) in
                       FStar_All.pipe_right uu____8044
                         (FStar_String.concat ", ") in
                     let uu____8096 =
                       let uu____8098 =
                         let uu____8102 = FStar_Util.set_elements uvt in
                         FStar_All.pipe_right uu____8102
                           (FStar_List.map
                              (fun u ->
                                 let uu____8115 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head in
                                 let uu____8117 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                 FStar_Util.format2 "(%s : %s)" uu____8115
                                   uu____8117)) in
                       FStar_All.pipe_right uu____8098
                         (FStar_String.concat ", ") in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8042
                       uu____8096
                   else ());
                  (let univs2 =
                     let uu____8131 = FStar_Util.set_elements uvt in
                     FStar_List.fold_left
                       (fun univs2 ->
                          fun uv ->
                            let uu____8143 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ in
                            FStar_Util.set_union univs2 uu____8143) univs1
                       uu____8131 in
                   let uvs = gen_uvars uvt in
                   (let uu____8150 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen") in
                    if uu____8150
                    then
                      let uu____8155 =
                        let uu____8157 =
                          let uu____8161 = FStar_Util.set_elements univs2 in
                          FStar_All.pipe_right uu____8161
                            (FStar_List.map
                               (fun u ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u))) in
                        FStar_All.pipe_right uu____8157
                          (FStar_String.concat ", ") in
                      let uu____8209 =
                        let uu____8211 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u ->
                                  let uu____8225 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head in
                                  let uu____8227 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                  FStar_Util.format2 "(%s : %s)" uu____8225
                                    uu____8227)) in
                        FStar_All.pipe_right uu____8211
                          (FStar_String.concat ", ") in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8155
                        uu____8209
                    else ());
                   (univs2, uvs, (lbname, e, c1)))) in
           let uu____8248 =
             let uu____8265 = FStar_List.hd lecs in
             univs_and_uvars_of_lec uu____8265 in
           match uu____8248 with
           | (univs1, uvs, lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____8355 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1) in
                 if uu____8355
                 then ()
                 else
                   (let uu____8360 = lec_hd in
                    match uu____8360 with
                    | (lb1, uu____8368, uu____8369) ->
                        let uu____8370 = lec2 in
                        (match uu____8370 with
                         | (lb2, uu____8378, uu____8379) ->
                             let msg =
                               let uu____8382 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____8384 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____8382 uu____8384 in
                             let uu____8387 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____8387)) in
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
                 let uu____8455 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1) in
                 if uu____8455
                 then ()
                 else
                   (let uu____8460 = lec_hd in
                    match uu____8460 with
                    | (lb1, uu____8468, uu____8469) ->
                        let uu____8470 = lec2 in
                        (match uu____8470 with
                         | (lb2, uu____8478, uu____8479) ->
                             let msg =
                               let uu____8482 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____8484 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____8482 uu____8484 in
                             let uu____8487 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____8487)) in
               let lecs1 =
                 let uu____8498 = FStar_List.tl lecs in
                 FStar_List.fold_right
                   (fun this_lec ->
                      fun lecs1 ->
                        let uu____8551 = univs_and_uvars_of_lec this_lec in
                        match uu____8551 with
                        | (this_univs, this_uvs, this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____8498 [] in
               let lecs2 = lec_hd :: lecs1 in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____8656 = lec_hd in
                   match uu____8656 with
                   | (lbname, e, c) ->
                       let uu____8666 =
                         let uu____8672 =
                           let uu____8674 =
                             FStar_Syntax_Print.term_to_string k in
                           let uu____8676 =
                             FStar_Syntax_Print.lbname_to_string lbname in
                           let uu____8678 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c) in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____8674 uu____8676 uu____8678 in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____8672) in
                       let uu____8682 = FStar_TypeChecker_Env.get_range env in
                       FStar_Errors.raise_error uu____8666 uu____8682 in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u ->
                         let uu____8701 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head in
                         match uu____8701 with
                         | FStar_Pervasives_Native.Some uu____8710 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____8718 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ in
                             let uu____8722 =
                               FStar_Syntax_Util.arrow_formals k in
                             (match uu____8722 with
                              | (bs, kres) ->
                                  ((let uu____8766 =
                                      let uu____8767 =
                                        let uu____8770 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres in
                                        FStar_Syntax_Util.unrefine uu____8770 in
                                      uu____8767.FStar_Syntax_Syntax.n in
                                    match uu____8766 with
                                    | FStar_Syntax_Syntax.Tm_type uu____8771
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres in
                                        let uu____8775 =
                                          let uu____8777 =
                                            FStar_Util.set_is_empty free in
                                          Prims.op_Negation uu____8777 in
                                        if uu____8775 then fail1 kres else ()
                                    | uu____8782 -> fail1 kres);
                                   (let a =
                                      let uu____8784 =
                                        let uu____8787 =
                                          FStar_TypeChecker_Env.get_range env in
                                        FStar_All.pipe_left
                                          (fun _8790 ->
                                             FStar_Pervasives_Native.Some
                                               _8790) uu____8787 in
                                      FStar_Syntax_Syntax.new_bv uu____8784
                                        kres in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____8798 ->
                                          let uu____8807 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Util.abs bs uu____8807
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_tot
                                                  kres)) in
                                    FStar_Syntax_Util.set_uvar
                                      u.FStar_Syntax_Syntax.ctx_uvar_head t;
                                    (a,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))))) in
               let gen_univs1 = gen_univs env univs1 in
               let gen_tvars = gen_types uvs in
               let ecs =
                 FStar_All.pipe_right lecs2
                   (FStar_List.map
                      (fun uu____8910 ->
                         match uu____8910 with
                         | (lbname, e, c) ->
                             let uu____8956 =
                               match (gen_tvars, gen_univs1) with
                               | ([], []) -> (e, c, [])
                               | uu____9017 ->
                                   let uu____9030 = (e, c) in
                                   (match uu____9030 with
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
                                                (fun uu____9070 ->
                                                   match uu____9070 with
                                                   | (x, uu____9076) ->
                                                       let uu____9077 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____9077)
                                                gen_tvars in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____9095 =
                                                let uu____9097 =
                                                  FStar_Util.right lbname in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____9097 in
                                              if uu____9095
                                              then
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  tm tvar_args
                                                  FStar_Pervasives_Native.None
                                                  tm.FStar_Syntax_Syntax.pos
                                              else tm in
                                            FStar_Syntax_InstFV.inst
                                              instantiate_lbname_with_app e1
                                          else e1 in
                                        let t =
                                          let uu____9106 =
                                            let uu____9107 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____9107.FStar_Syntax_Syntax.n in
                                          match uu____9106 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs, cod) ->
                                              let uu____9132 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____9132 with
                                               | (bs1, cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____9143 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____9147 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____9147, gen_tvars)) in
                             (match uu____8956 with
                              | (e1, c1, gvs) ->
                                  (lbname, gen_univs1, e1, c1, gvs)))) in
               FStar_Pervasives_Native.Some ecs)
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
        (let uu____9294 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____9294
         then
           let uu____9297 =
             let uu____9299 =
               FStar_List.map
                 (fun uu____9314 ->
                    match uu____9314 with
                    | (lb, uu____9323, uu____9324) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_All.pipe_right uu____9299 (FStar_String.concat ", ") in
           FStar_Util.print1 "Generalizing: %s\n" uu____9297
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____9350 ->
                match uu____9350 with
                | (l, t, c) -> gather_free_univnames env t) lecs in
         let generalized_lecs =
           let uu____9379 = gen env is_rec lecs in
           match uu____9379 with
           | FStar_Pervasives_Native.None ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____9478 ->
                       match uu____9478 with | (l, t, c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____9540 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 if uu____9540
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____9588 ->
                           match uu____9588 with
                           | (l, us, e, c, gvs) ->
                               let uu____9622 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos in
                               let uu____9624 =
                                 FStar_Syntax_Print.lbname_to_string l in
                               let uu____9626 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c) in
                               let uu____9628 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____9630 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____9622 uu____9624 uu____9626 uu____9628
                                 uu____9630))
                 else ());
                luecs) in
         FStar_List.map2
           (fun univnames1 ->
              fun uu____9675 ->
                match uu____9675 with
                | (l, generalized_univs, t, c, gvs) ->
                    let uu____9719 =
                      check_universe_generalization univnames1
                        generalized_univs t in
                    (l, uu____9719, t, c, gvs)) univnames_lecs
           generalized_lecs)
let (check_and_ascribe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun e ->
      fun t1 ->
        fun t2 ->
          let env1 =
            FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
          let check1 env2 t11 t21 =
            if env2.FStar_TypeChecker_Env.use_eq
            then FStar_TypeChecker_Rel.try_teq true env2 t11 t21
            else
              (let uu____9780 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21 in
               match uu____9780 with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____9786 = FStar_TypeChecker_Env.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _9789 -> FStar_Pervasives_Native.Some _9789)
                     uu____9786) in
          let is_var e1 =
            let uu____9797 =
              let uu____9798 = FStar_Syntax_Subst.compress e1 in
              uu____9798.FStar_Syntax_Syntax.n in
            match uu____9797 with
            | FStar_Syntax_Syntax.Tm_name uu____9802 -> true
            | uu____9804 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1273_9825 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1273_9825.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1273_9825.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____9826 -> e2 in
          let env2 =
            let uu___1276_9828 = env1 in
            let uu____9829 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1276_9828.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1276_9828.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1276_9828.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1276_9828.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1276_9828.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1276_9828.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1276_9828.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1276_9828.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1276_9828.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1276_9828.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1276_9828.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1276_9828.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1276_9828.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1276_9828.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1276_9828.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1276_9828.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1276_9828.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____9829;
              FStar_TypeChecker_Env.is_iface =
                (uu___1276_9828.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1276_9828.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1276_9828.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1276_9828.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1276_9828.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1276_9828.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1276_9828.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1276_9828.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1276_9828.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1276_9828.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1276_9828.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1276_9828.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1276_9828.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1276_9828.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1276_9828.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1276_9828.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1276_9828.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1276_9828.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1276_9828.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1276_9828.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1276_9828.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1276_9828.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1276_9828.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1276_9828.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1276_9828.FStar_TypeChecker_Env.nbe)
            } in
          let uu____9831 = check1 env2 t1 t2 in
          match uu____9831 with
          | FStar_Pervasives_Native.None ->
              let uu____9838 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1 in
              let uu____9844 = FStar_TypeChecker_Env.get_range env2 in
              FStar_Errors.raise_error uu____9838 uu____9844
          | FStar_Pervasives_Native.Some g ->
              ((let uu____9851 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____9851
                then
                  let uu____9856 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____9856
                else ());
               (let uu____9862 = decorate e t2 in (uu____9862, g)))
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp -> (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env ->
    fun g ->
      fun lc ->
        (let uu____9890 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____9890
         then
           let uu____9893 = FStar_Syntax_Print.lcomp_to_string lc in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____9893
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_Syntax_Util.is_pure_lcomp lc in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
         let uu____9907 = FStar_Syntax_Util.is_total_lcomp lc in
         if uu____9907
         then
           let uu____9915 = discharge g1 in
           let uu____9917 = FStar_Syntax_Syntax.lcomp_comp lc in
           (uu____9915, uu____9917)
         else
           (let c = FStar_Syntax_Syntax.lcomp_comp lc in
            let steps =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.NoFullNorm;
              FStar_TypeChecker_Env.DoNotUnfoldPureLets] in
            let c1 =
              let uu____9926 =
                let uu____9927 =
                  let uu____9928 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                  FStar_All.pipe_right uu____9928 FStar_Syntax_Syntax.mk_Comp in
                FStar_All.pipe_right uu____9927
                  (FStar_TypeChecker_Normalize.normalize_comp steps env) in
              FStar_All.pipe_right uu____9926
                (FStar_TypeChecker_Env.comp_to_comp_typ env) in
            let md =
              FStar_TypeChecker_Env.get_effect_decl env
                c1.FStar_Syntax_Syntax.effect_name in
            let uu____9930 = destruct_comp c1 in
            match uu____9930 with
            | (u_t, t, wp) ->
                let vc =
                  let uu____9948 = FStar_TypeChecker_Env.get_range env in
                  let uu____9949 =
                    let uu____9954 =
                      FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                        md.FStar_Syntax_Syntax.trivial in
                    let uu____9955 =
                      let uu____9956 = FStar_Syntax_Syntax.as_arg t in
                      let uu____9965 =
                        let uu____9976 = FStar_Syntax_Syntax.as_arg wp in
                        [uu____9976] in
                      uu____9956 :: uu____9965 in
                    FStar_Syntax_Syntax.mk_Tm_app uu____9954 uu____9955 in
                  uu____9949 FStar_Pervasives_Native.None uu____9948 in
                ((let uu____10010 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Simplification") in
                  if uu____10010
                  then
                    let uu____10015 = FStar_Syntax_Print.term_to_string vc in
                    FStar_Util.print1 "top-level VC: %s\n" uu____10015
                  else ());
                 (let g2 =
                    let uu____10021 =
                      FStar_All.pipe_left
                        FStar_TypeChecker_Env.guard_of_guard_formula
                        (FStar_TypeChecker_Common.NonTrivial vc) in
                    FStar_TypeChecker_Env.conj_guard g1 uu____10021 in
                  let uu____10022 = discharge g2 in
                  let uu____10024 = FStar_Syntax_Syntax.mk_Comp c1 in
                  (uu____10022, uu____10024)))))
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1 ->
    fun seen_args ->
      let short_bin_op f uu___8_10058 =
        match uu___8_10058 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1, uu____10068)::[] -> f fst1
        | uu____10093 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____10105 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____10105
          (fun _10106 -> FStar_TypeChecker_Common.NonTrivial _10106) in
      let op_or_e e =
        let uu____10117 =
          let uu____10118 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____10118 in
        FStar_All.pipe_right uu____10117
          (fun _10121 -> FStar_TypeChecker_Common.NonTrivial _10121) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _10128 -> FStar_TypeChecker_Common.NonTrivial _10128) in
      let op_or_t t =
        let uu____10139 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____10139
          (fun _10142 -> FStar_TypeChecker_Common.NonTrivial _10142) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _10149 -> FStar_TypeChecker_Common.NonTrivial _10149) in
      let short_op_ite uu___9_10155 =
        match uu___9_10155 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard, uu____10165)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard, uu____10192)::[] ->
            let uu____10233 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____10233
              (fun _10234 -> FStar_TypeChecker_Common.NonTrivial _10234)
        | uu____10235 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____10247 =
          let uu____10255 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____10255) in
        let uu____10263 =
          let uu____10273 =
            let uu____10281 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____10281) in
          let uu____10289 =
            let uu____10299 =
              let uu____10307 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____10307) in
            let uu____10315 =
              let uu____10325 =
                let uu____10333 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____10333) in
              let uu____10341 =
                let uu____10351 =
                  let uu____10359 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____10359) in
                [uu____10351; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____10325 :: uu____10341 in
            uu____10299 :: uu____10315 in
          uu____10273 :: uu____10289 in
        uu____10247 :: uu____10263 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____10421 =
            FStar_Util.find_map table
              (fun uu____10436 ->
                 match uu____10436 with
                 | (x, mk1) ->
                     let uu____10453 = FStar_Ident.lid_equals x lid in
                     if uu____10453
                     then
                       let uu____10458 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____10458
                     else FStar_Pervasives_Native.None) in
          (match uu____10421 with
           | FStar_Pervasives_Native.None -> FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____10462 -> FStar_TypeChecker_Common.Trivial
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l ->
    let uu____10470 =
      let uu____10471 = FStar_Syntax_Util.un_uinst l in
      uu____10471.FStar_Syntax_Syntax.n in
    match uu____10470 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____10476 -> false
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env ->
    fun bs ->
      let pos bs1 =
        match bs1 with
        | (hd1, uu____10512)::uu____10513 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____10532 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____10541, FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____10542))::uu____10543 -> bs
      | uu____10561 ->
          let uu____10562 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____10562 with
           | FStar_Pervasives_Native.None -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____10566 =
                 let uu____10567 = FStar_Syntax_Subst.compress t in
                 uu____10567.FStar_Syntax_Syntax.n in
               (match uu____10566 with
                | FStar_Syntax_Syntax.Tm_arrow (bs', uu____10571) ->
                    let uu____10592 =
                      FStar_Util.prefix_until
                        (fun uu___10_10632 ->
                           match uu___10_10632 with
                           | (uu____10640, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10641)) ->
                               false
                           | uu____10646 -> true) bs' in
                    (match uu____10592 with
                     | FStar_Pervasives_Native.None -> bs
                     | FStar_Pervasives_Native.Some
                         ([], uu____10682, uu____10683) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps, uu____10755, uu____10756) ->
                         let uu____10829 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____10849 ->
                                   match uu____10849 with
                                   | (x, uu____10858) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____10829
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____10907 ->
                                     match uu____10907 with
                                     | (x, i) ->
                                         let uu____10926 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____10926, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____10937 -> bs))
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
            let uu____10966 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1)) in
            if uu____10966
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
  fun env ->
    fun e ->
      fun c ->
        fun t ->
          let m = FStar_TypeChecker_Env.norm_eff_name env c in
          let uu____10997 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____10997
          then e
          else
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_meta
                 (e, (FStar_Syntax_Syntax.Meta_monadic (m, t))))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
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
        (let uu____11040 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____11040
         then
           ((let uu____11045 = FStar_Ident.text_of_lid lident in
             d uu____11045);
            (let uu____11047 = FStar_Ident.text_of_lid lident in
             let uu____11049 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____11047 uu____11049))
         else ());
        (let fv =
           let uu____11055 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____11055
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
         let uu____11067 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___1434_11069 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1434_11069.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1434_11069.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1434_11069.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1434_11069.FStar_Syntax_Syntax.sigattrs)
           }), uu____11067))
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env ->
    fun se ->
      let visibility uu___11_11087 =
        match uu___11_11087 with
        | FStar_Syntax_Syntax.Private -> true
        | uu____11090 -> false in
      let reducibility uu___12_11098 =
        match uu___12_11098 with
        | FStar_Syntax_Syntax.Abstract -> true
        | FStar_Syntax_Syntax.Irreducible -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> true
        | FStar_Syntax_Syntax.Visible_default -> true
        | FStar_Syntax_Syntax.Inline_for_extraction -> true
        | uu____11105 -> false in
      let assumption uu___13_11113 =
        match uu___13_11113 with
        | FStar_Syntax_Syntax.Assumption -> true
        | FStar_Syntax_Syntax.New -> true
        | uu____11117 -> false in
      let reification uu___14_11125 =
        match uu___14_11125 with
        | FStar_Syntax_Syntax.Reifiable -> true
        | FStar_Syntax_Syntax.Reflectable uu____11128 -> true
        | uu____11130 -> false in
      let inferred uu___15_11138 =
        match uu___15_11138 with
        | FStar_Syntax_Syntax.Discriminator uu____11140 -> true
        | FStar_Syntax_Syntax.Projector uu____11142 -> true
        | FStar_Syntax_Syntax.RecordType uu____11148 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11158 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor -> true
        | FStar_Syntax_Syntax.HasMaskedEffect -> true
        | FStar_Syntax_Syntax.Effect -> true
        | uu____11171 -> false in
      let has_eq uu___16_11179 =
        match uu___16_11179 with
        | FStar_Syntax_Syntax.Noeq -> true
        | FStar_Syntax_Syntax.Unopteq -> true
        | uu____11183 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____11262 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private -> true
        | uu____11269 -> true in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic))) in
      let uu____11280 =
        let uu____11282 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___17_11288 ->
                  match uu___17_11288 with
                  | FStar_Syntax_Syntax.OnlyName -> true
                  | uu____11291 -> false)) in
        FStar_All.pipe_right uu____11282 Prims.op_Negation in
      if uu____11280
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x -> fun y -> x = y) quals in
        let err' msg =
          let uu____11312 =
            let uu____11318 =
              let uu____11320 = FStar_Syntax_Print.quals_to_string quals in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____11320 msg in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____11318) in
          FStar_Errors.raise_error uu____11312 r in
        let err msg = err' (Prims.op_Hat ": " msg) in
        let err'1 uu____11338 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____11346 =
            let uu____11348 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____11348 in
          if uu____11346 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec, uu____11358), uu____11359)
              ->
              ((let uu____11371 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____11371
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____11380 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x -> (assumption x) || (has_eq x))) in
                if uu____11380
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11391 ->
              let uu____11400 =
                let uu____11402 =
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
                Prims.op_Negation uu____11402 in
              if uu____11400 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11412 ->
              let uu____11419 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____11419 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11427 ->
              let uu____11434 =
                let uu____11436 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____11436 in
              if uu____11434 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11446 ->
              let uu____11447 =
                let uu____11449 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11449 in
              if uu____11447 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11459 ->
              let uu____11460 =
                let uu____11462 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11462 in
              if uu____11460 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11472 ->
              let uu____11485 =
                let uu____11487 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____11487 in
              if uu____11485 then err'1 () else ()
          | uu____11497 -> ()))
      else ()
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g ->
    fun t ->
      let has_erased_for_extraction_attr fv =
        let uu____11520 =
          let uu____11525 =
            FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv in
          FStar_All.pipe_right uu____11525
            (FStar_TypeChecker_Env.lookup_attrs_of_lid g) in
        FStar_All.pipe_right uu____11520
          (fun l_opt ->
             (FStar_Util.is_some l_opt) &&
               (let uu____11544 = FStar_All.pipe_right l_opt FStar_Util.must in
                FStar_All.pipe_right uu____11544
                  (FStar_List.existsb
                     (fun t1 ->
                        let uu____11562 =
                          let uu____11563 = FStar_Syntax_Subst.compress t1 in
                          uu____11563.FStar_Syntax_Syntax.n in
                        match uu____11562 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            FStar_Ident.lid_equals
                              (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              FStar_Parser_Const.must_erase_for_extraction_attr
                            -> true
                        | uu____11569 -> false)))) in
      let rec aux_whnf env t1 =
        let uu____11595 =
          let uu____11596 = FStar_Syntax_Subst.compress t1 in
          uu____11596.FStar_Syntax_Syntax.n in
        match uu____11595 with
        | FStar_Syntax_Syntax.Tm_type uu____11600 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (has_erased_for_extraction_attr fv)
        | FStar_Syntax_Syntax.Tm_arrow uu____11603 ->
            let uu____11618 = FStar_Syntax_Util.arrow_formals_comp t1 in
            (match uu____11618 with
             | (bs, c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs in
                 let uu____11651 = FStar_Syntax_Util.is_pure_comp c in
                 if uu____11651
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____11657;
               FStar_Syntax_Syntax.index = uu____11658;
               FStar_Syntax_Syntax.sort = t2;_},
             uu____11660)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____11669, uu____11670) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1, uu____11712::[]) ->
            let uu____11751 =
              let uu____11752 = FStar_Syntax_Util.un_uinst head1 in
              uu____11752.FStar_Syntax_Syntax.n in
            (match uu____11751 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.erased_lid)
                   || (has_erased_for_extraction_attr fv)
             | uu____11757 -> false)
        | uu____11759 -> false
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
            FStar_TypeChecker_Env.Iota] env t1 in
        let res = aux_whnf env t2 in
        (let uu____11769 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction") in
         if uu____11769
         then
           let uu____11774 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____11774
         else ());
        res in
      aux g t