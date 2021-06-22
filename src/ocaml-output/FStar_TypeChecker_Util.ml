open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option *
    FStar_TypeChecker_Common.lcomp)
let (report : FStar_TypeChecker_Env.env -> Prims.string Prims.list -> unit) =
  fun env ->
    fun errs ->
      let uu___ = FStar_TypeChecker_Env.get_range env in
      let uu___1 = FStar_TypeChecker_Err.failed_to_prove_specification errs in
      FStar_Errors.log_issue uu___ uu___1
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
          let uu___ = (FStar_Options.eager_subtyping ()) || solve_deferred in
          if uu___
          then
            let uu___1 =
              FStar_All.pipe_right g.FStar_TypeChecker_Common.deferred
                (FStar_List.partition
                   (fun uu___2 ->
                      match uu___2 with
                      | (uu___3, uu___4, p) ->
                          FStar_TypeChecker_Rel.flex_prob_closing env xs p)) in
            match uu___1 with
            | (solve_now, defer) ->
                ((let uu___3 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel") in
                  if uu___3
                  then
                    (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                     FStar_List.iter
                       (fun uu___6 ->
                          match uu___6 with
                          | (uu___7, s, p) ->
                              let uu___8 =
                                FStar_TypeChecker_Rel.prob_to_string env p in
                              FStar_Util.print2 "%s: %s\n" s uu___8)
                       solve_now;
                     FStar_Util.print_string " ...DEFERRED THE REST:\n";
                     FStar_List.iter
                       (fun uu___8 ->
                          match uu___8 with
                          | (uu___9, s, p) ->
                              let uu___10 =
                                FStar_TypeChecker_Rel.prob_to_string env p in
                              FStar_Util.print2 "%s: %s\n" s uu___10) defer;
                     FStar_Util.print_string "END\n")
                  else ());
                 (let g1 =
                    FStar_TypeChecker_Rel.solve_non_tactic_deferred_constraints
                      env
                      (let uu___3 = g in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___3.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred_to_tac =
                           (uu___3.FStar_TypeChecker_Common.deferred_to_tac);
                         FStar_TypeChecker_Common.deferred = solve_now;
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___3.FStar_TypeChecker_Common.univ_ineqs);
                         FStar_TypeChecker_Common.implicits =
                           (uu___3.FStar_TypeChecker_Common.implicits)
                       }) in
                  let g2 =
                    let uu___3 = g1 in
                    {
                      FStar_TypeChecker_Common.guard_f =
                        (uu___3.FStar_TypeChecker_Common.guard_f);
                      FStar_TypeChecker_Common.deferred_to_tac =
                        (uu___3.FStar_TypeChecker_Common.deferred_to_tac);
                      FStar_TypeChecker_Common.deferred = defer;
                      FStar_TypeChecker_Common.univ_ineqs =
                        (uu___3.FStar_TypeChecker_Common.univ_ineqs);
                      FStar_TypeChecker_Common.implicits =
                        (uu___3.FStar_TypeChecker_Common.implicits)
                    } in
                  g2))
          else g
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r ->
    fun t ->
      let uvs = FStar_Syntax_Free.uvars t in
      let uu___ =
        let uu___1 = FStar_Util.set_is_empty uvs in Prims.op_Negation uu___1 in
      if uu___
      then
        let us =
          let uu___1 =
            let uu___2 = FStar_Util.set_elements uvs in
            FStar_List.map
              (fun u ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu___2 in
          FStar_All.pipe_right uu___1 (FStar_String.concat ", ") in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu___5 =
            let uu___6 =
              let uu___7 = FStar_Syntax_Print.term_to_string t in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu___7 in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu___6) in
          FStar_Errors.log_issue r uu___5);
         FStar_Options.pop ())
      else ()
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ *
        FStar_Syntax_Syntax.term * Prims.bool))
  =
  fun env ->
    fun uu___ ->
      match uu___ with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars;
          FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu___1;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu___2;
          FStar_Syntax_Syntax.lbpos = uu___3;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname in
          let t1 = FStar_Syntax_Subst.compress t in
          let uu___4 = FStar_Syntax_Subst.univ_var_opening univ_vars in
          (match uu___4 with
           | (u_subst, univ_vars1) ->
               let e1 = FStar_Syntax_Subst.subst u_subst e in
               let t2 = FStar_Syntax_Subst.subst u_subst t1 in
               ((let uu___6 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Dec") in
                 if uu___6
                 then
                   let uu___7 = FStar_Syntax_Print.term_to_string e1 in
                   let uu___8 = FStar_Syntax_Print.term_to_string t2 in
                   FStar_Util.print2
                     "extract_let_rec_annotation lbdef=%s; lbtyp=%s\n" uu___7
                     uu___8
                 else ());
                (let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 let un_arrow t3 =
                   let uu___6 =
                     let uu___7 = FStar_Syntax_Subst.compress t3 in
                     uu___7.FStar_Syntax_Syntax.n in
                   match uu___6 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                       FStar_Syntax_Subst.open_comp bs c
                   | uu___7 ->
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_LetRecArgumentMismatch,
                           "Recursive functions must be introduced at arrow types")
                         rng in
                 let reconcile_let_rec_ascription_and_body_type tarr
                   lbtyp_opt =
                   let get_decreases c =
                     FStar_All.pipe_right (FStar_Syntax_Util.comp_flags c)
                       (FStar_Util.prefix_until
                          (fun uu___6 ->
                             match uu___6 with
                             | FStar_Syntax_Syntax.DECREASES uu___7 -> true
                             | uu___7 -> false)) in
                   match lbtyp_opt with
                   | FStar_Pervasives_Native.None ->
                       let uu___6 = un_arrow tarr in
                       (match uu___6 with
                        | (bs, c) ->
                            let uu___7 = get_decreases c in
                            (match uu___7 with
                             | FStar_Pervasives_Native.Some
                                 (pfx, FStar_Syntax_Syntax.DECREASES d, sfx)
                                 ->
                                 let c1 =
                                   FStar_Syntax_Util.comp_set_flags c
                                     (FStar_List.append pfx sfx) in
                                 let uu___8 = FStar_Syntax_Util.arrow bs c1 in
                                 (uu___8, tarr, true)
                             | uu___8 -> (tarr, tarr, true)))
                   | FStar_Pervasives_Native.Some annot ->
                       let uu___6 = un_arrow tarr in
                       (match uu___6 with
                        | (bs, c) ->
                            let uu___7 = un_arrow annot in
                            (match uu___7 with
                             | (bs', c') ->
                                 (if
                                    (FStar_List.length bs) <>
                                      (FStar_List.length bs')
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_LetRecArgumentMismatch,
                                        "Arity mismatch on let rec annotation")
                                      rng
                                  else ();
                                  (let move_decreases d flags flags' =
                                     let d' =
                                       let s =
                                         FStar_Syntax_Util.rename_binders bs
                                           bs' in
                                       FStar_Syntax_Subst.subst_decreasing_order
                                         s d in
                                     let c1 =
                                       FStar_Syntax_Util.comp_set_flags c
                                         flags in
                                     let tarr1 =
                                       FStar_Syntax_Util.arrow bs c1 in
                                     let c'1 =
                                       FStar_Syntax_Util.comp_set_flags c'
                                         ((FStar_Syntax_Syntax.DECREASES d')
                                         :: flags') in
                                     let tannot =
                                       FStar_Syntax_Util.arrow bs' c'1 in
                                     (tarr1, tannot, true) in
                                   let uu___9 =
                                     let uu___10 = get_decreases c in
                                     let uu___11 = get_decreases c' in
                                     (uu___10, uu___11) in
                                   match uu___9 with
                                   | (FStar_Pervasives_Native.None, uu___10)
                                       -> (tarr, annot, false)
                                   | (FStar_Pervasives_Native.Some
                                      (pfx, FStar_Syntax_Syntax.DECREASES d,
                                       sfx),
                                      FStar_Pervasives_Native.Some
                                      (pfx', FStar_Syntax_Syntax.DECREASES
                                       d', sfx')) ->
                                       (FStar_Errors.log_issue rng
                                          (FStar_Errors.Warning_DeprecatedGeneric,
                                            "Multiple decreases clauses on this definition; the decreases clause on the declaration is ignored, please remove it");
                                        move_decreases d
                                          (FStar_List.append pfx sfx)
                                          (FStar_List.append pfx' sfx'))
                                   | (FStar_Pervasives_Native.Some
                                      (pfx, FStar_Syntax_Syntax.DECREASES d,
                                       sfx),
                                      FStar_Pervasives_Native.None) ->
                                       move_decreases d
                                         (FStar_List.append pfx sfx)
                                         (FStar_Syntax_Util.comp_flags c')
                                   | uu___10 -> failwith "Impossible")))) in
                 let extract_annot_from_body lbtyp_opt =
                   let rec aux_lbdef e2 =
                     let e3 = FStar_Syntax_Subst.compress e2 in
                     match e3.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_meta (e', m) ->
                         let uu___6 = aux_lbdef e' in
                         (match uu___6 with
                          | (t3, e'1, recheck) ->
                              (t3,
                                (let uu___7 = e3 in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (FStar_Syntax_Syntax.Tm_meta (e'1, m));
                                   FStar_Syntax_Syntax.pos =
                                     (uu___7.FStar_Syntax_Syntax.pos);
                                   FStar_Syntax_Syntax.vars =
                                     (uu___7.FStar_Syntax_Syntax.vars)
                                 }), recheck))
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (e', (FStar_Pervasives.Inr c, tac_opt), lopt) ->
                         let uu___6 = FStar_Syntax_Util.is_total_comp c in
                         if uu___6
                         then
                           let uu___7 =
                             reconcile_let_rec_ascription_and_body_type
                               (FStar_Syntax_Util.comp_result c) lbtyp_opt in
                           (match uu___7 with
                            | (t3, lbtyp, recheck) ->
                                let e4 =
                                  let uu___8 = e3 in
                                  let uu___9 =
                                    let uu___10 =
                                      let uu___11 =
                                        let uu___12 =
                                          let uu___13 =
                                            FStar_Syntax_Syntax.mk_Total t3 in
                                          FStar_Pervasives.Inr uu___13 in
                                        (uu___12, tac_opt) in
                                      (e', uu___11, lopt) in
                                    FStar_Syntax_Syntax.Tm_ascribed uu___10 in
                                  {
                                    FStar_Syntax_Syntax.n = uu___9;
                                    FStar_Syntax_Syntax.pos =
                                      (uu___8.FStar_Syntax_Syntax.pos);
                                    FStar_Syntax_Syntax.vars =
                                      (uu___8.FStar_Syntax_Syntax.vars)
                                  } in
                                (lbtyp, e4, recheck))
                         else
                           (let uu___8 =
                              let uu___9 =
                                let uu___10 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.format1
                                  "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                  uu___10 in
                              (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                uu___9) in
                            FStar_Errors.raise_error uu___8 rng)
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (e', (FStar_Pervasives.Inl t3, tac_opt), lopt) ->
                         let uu___6 =
                           reconcile_let_rec_ascription_and_body_type t3
                             lbtyp_opt in
                         (match uu___6 with
                          | (t4, lbtyp, recheck) ->
                              let e4 =
                                let uu___7 = e3 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_ascribed
                                       (e',
                                         ((FStar_Pervasives.Inl t4), tac_opt),
                                         lopt));
                                  FStar_Syntax_Syntax.pos =
                                    (uu___7.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___7.FStar_Syntax_Syntax.vars)
                                } in
                              (lbtyp, e4, recheck))
                     | FStar_Syntax_Syntax.Tm_abs uu___6 ->
                         let uu___7 =
                           FStar_Syntax_Util.abs_formals_maybe_unascribe_body
                             false e3 in
                         (match uu___7 with
                          | (bs, body, rcopt) ->
                              let mk_comp t3 =
                                let uu___8 = FStar_Options.ml_ish () in
                                if uu___8
                                then
                                  FStar_Syntax_Util.ml_comp t3
                                    t3.FStar_Syntax_Syntax.pos
                                else FStar_Syntax_Syntax.mk_Total t3 in
                              let mk_arrow c = FStar_Syntax_Util.arrow bs c in
                              let rec aux_abs_body body1 =
                                let body2 = FStar_Syntax_Subst.compress body1 in
                                match body2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_meta (body3, m) ->
                                    let uu___8 = aux_abs_body body3 in
                                    (match uu___8 with
                                     | (t3, body', recheck) ->
                                         let body4 =
                                           let uu___9 = body3 in
                                           {
                                             FStar_Syntax_Syntax.n =
                                               (FStar_Syntax_Syntax.Tm_meta
                                                  (body', m));
                                             FStar_Syntax_Syntax.pos =
                                               (uu___9.FStar_Syntax_Syntax.pos);
                                             FStar_Syntax_Syntax.vars =
                                               (uu___9.FStar_Syntax_Syntax.vars)
                                           } in
                                         (t3, body4, recheck))
                                | FStar_Syntax_Syntax.Tm_ascribed
                                    (uu___8,
                                     (FStar_Pervasives.Inl t3, uu___9),
                                     uu___10)
                                    ->
                                    (match lbtyp_opt with
                                     | FStar_Pervasives_Native.Some lbtyp ->
                                         (lbtyp, body2, false)
                                     | FStar_Pervasives_Native.None ->
                                         let t4 =
                                           let uu___11 = mk_comp t3 in
                                           mk_arrow uu___11 in
                                         (t4, body2, true))
                                | FStar_Syntax_Syntax.Tm_ascribed
                                    (body',
                                     (FStar_Pervasives.Inr c, tac_opt), lopt)
                                    ->
                                    let tarr = mk_arrow c in
                                    let uu___8 =
                                      reconcile_let_rec_ascription_and_body_type
                                        tarr lbtyp_opt in
                                    (match uu___8 with
                                     | (tarr1, lbtyp, recheck) ->
                                         let uu___9 = un_arrow tarr1 in
                                         (match uu___9 with
                                          | (bs', c1) ->
                                              if
                                                (FStar_List.length bs') <>
                                                  (FStar_List.length bs)
                                              then failwith "Impossible"
                                              else
                                                (let subst =
                                                   FStar_Syntax_Util.rename_binders
                                                     bs' bs in
                                                 let c2 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     subst c1 in
                                                 let body3 =
                                                   let uu___11 = body2 in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       (FStar_Syntax_Syntax.Tm_ascribed
                                                          (body',
                                                            ((FStar_Pervasives.Inr
                                                                c2), tac_opt),
                                                            lopt));
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___11.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___11.FStar_Syntax_Syntax.vars)
                                                   } in
                                                 (lbtyp, body3, recheck))))
                                | uu___8 ->
                                    (match lbtyp_opt with
                                     | FStar_Pervasives_Native.Some lbtyp ->
                                         (lbtyp, body2, false)
                                     | FStar_Pervasives_Native.None ->
                                         let tarr =
                                           let uu___9 =
                                             mk_comp FStar_Syntax_Syntax.tun in
                                           mk_arrow uu___9 in
                                         (tarr, body2, true)) in
                              let uu___8 = aux_abs_body body in
                              (match uu___8 with
                               | (lbtyp, body1, recheck) ->
                                   let uu___9 =
                                     FStar_Syntax_Util.abs bs body1 rcopt in
                                   (lbtyp, uu___9, recheck))) in
                   aux_lbdef e1 in
                 match t2.FStar_Syntax_Syntax.n with
                 | FStar_Syntax_Syntax.Tm_unknown ->
                     let uu___6 =
                       extract_annot_from_body FStar_Pervasives_Native.None in
                     (match uu___6 with
                      | (lbtyp, e2, uu___7) -> (univ_vars1, lbtyp, e2, true))
                 | uu___6 ->
                     let uu___7 = FStar_Syntax_Util.arrow_formals_comp t2 in
                     (match uu___7 with
                      | (uu___8, c) ->
                          let uu___9 =
                            let uu___10 =
                              let uu___11 =
                                FStar_All.pipe_right
                                  (FStar_Syntax_Util.comp_effect_name c)
                                  (FStar_TypeChecker_Env.lookup_effect_quals
                                     env1) in
                              FStar_All.pipe_right uu___11
                                (FStar_List.contains
                                   FStar_Syntax_Syntax.TotalEffect) in
                            Prims.op_Negation uu___10 in
                          if uu___9
                          then (univ_vars1, t2, e1, false)
                          else
                            (let uu___11 =
                               extract_annot_from_body
                                 (FStar_Pervasives_Native.Some t2) in
                             match uu___11 with
                             | (lbtyp, e2, check_lbtyp) ->
                                 (univ_vars1, lbtyp, e2, check_lbtyp))))))
let rec (decorated_pattern_as_term :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun pat ->
    let mk f = FStar_Syntax_Syntax.mk f pat.FStar_Syntax_Syntax.p in
    let pat_as_arg uu___ =
      match uu___ with
      | (p, i) ->
          let uu___1 = decorated_pattern_as_term p in
          (match uu___1 with
           | (vars, te) ->
               let uu___2 =
                 let uu___3 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu___3) in
               (vars, uu___2)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu___ = mk (FStar_Syntax_Syntax.Tm_constant c) in ([], uu___)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu___ = mk (FStar_Syntax_Syntax.Tm_name x) in ([x], uu___)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu___ = mk (FStar_Syntax_Syntax.Tm_name x) in ([x], uu___)
    | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
        let uu___ =
          let uu___1 = FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu___1 FStar_List.unzip in
        (match uu___ with
         | (vars, args) ->
             let vars1 = FStar_List.flatten vars in
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu___4, args) in
                 FStar_Syntax_Syntax.Tm_app uu___3 in
               mk uu___2 in
             (vars1, uu___1))
    | FStar_Syntax_Syntax.Pat_dot_term (x, e) -> ([], e)
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu___, uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu___, uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd::uu___ -> FStar_Pervasives_Native.Some hd)
let (lcomp_univ_opt :
  FStar_TypeChecker_Common.lcomp ->
    (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option *
      FStar_TypeChecker_Common.guard_t))
  =
  fun lc ->
    let uu___ = FStar_All.pipe_right lc FStar_TypeChecker_Common.lcomp_comp in
    FStar_All.pipe_right uu___
      (fun uu___1 -> match uu___1 with | (c, g) -> ((comp_univ_opt c), g))
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
            let uu___ =
              let uu___1 =
                let uu___2 = FStar_Syntax_Syntax.as_arg wp in [uu___2] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu___1;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu___
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
        let err uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Print.term_to_string repr in
              let uu___4 = FStar_Util.string_of_bool is_layered in
              FStar_Util.format2
                "Could not get effect args from repr %s with is_layered %s"
                uu___3 uu___4 in
            (FStar_Errors.Fatal_UnexpectedEffect, uu___2) in
          FStar_Errors.raise_error uu___1 r in
        let repr1 = FStar_Syntax_Subst.compress repr in
        if is_layered
        then
          match repr1.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_app (uu___, uu___1::is) ->
              FStar_All.pipe_right is
                (FStar_List.map FStar_Pervasives_Native.fst)
          | uu___ -> err ()
        else
          (match repr1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (uu___1, c) ->
               let uu___2 =
                 FStar_All.pipe_right c FStar_Syntax_Util.comp_to_comp_typ in
               FStar_All.pipe_right uu___2
                 (fun ct ->
                    FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                      (FStar_List.map FStar_Pervasives_Native.fst))
           | uu___1 -> err ())
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
                let uu___ =
                  let uu___1 =
                    FStar_TypeChecker_Env.lid_exists env
                      FStar_Parser_Const.effect_GTot_lid in
                  FStar_All.pipe_left Prims.op_Negation uu___1 in
                if uu___
                then FStar_Syntax_Syntax.mk_Total a
                else
                  (let uu___2 = FStar_Syntax_Util.is_unit a in
                   if uu___2
                   then
                     FStar_Syntax_Syntax.mk_Total' a
                       (FStar_Pervasives_Native.Some
                          FStar_Syntax_Syntax.U_zero)
                   else
                     (let wp =
                        let uu___4 =
                          env.FStar_TypeChecker_Env.lax &&
                            (FStar_Options.ml_ish ()) in
                        if uu___4
                        then FStar_Syntax_Syntax.tun
                        else
                          (let ret_wp =
                             FStar_All.pipe_right ed
                               FStar_Syntax_Util.get_return_vc_combinator in
                           let uu___6 =
                             FStar_TypeChecker_Env.inst_effect_fun_with 
                               [u_a] env ed ret_wp in
                           let uu___7 =
                             let uu___8 = FStar_Syntax_Syntax.as_arg a in
                             let uu___9 =
                               let uu___10 = FStar_Syntax_Syntax.as_arg e in
                               [uu___10] in
                             uu___8 :: uu___9 in
                           FStar_Syntax_Syntax.mk_Tm_app uu___6 uu___7
                             e.FStar_Syntax_Syntax.pos) in
                      mk_comp ed u_a a wp [FStar_Syntax_Syntax.RETURN])) in
              (let uu___1 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Return") in
               if uu___1
               then
                 let uu___2 =
                   FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                 let uu___3 = FStar_Syntax_Print.term_to_string e in
                 let uu___4 =
                   FStar_TypeChecker_Normalize.comp_to_string env c in
                 FStar_Util.print3 "(%s) returning %s at comp type %s\n"
                   uu___2 uu___3 uu___4
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
              (let uu___1 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "LayeredEffects") in
               if uu___1
               then
                 let uu___2 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                 let uu___3 = FStar_Syntax_Print.univ_to_string u_a in
                 let uu___4 = FStar_Syntax_Print.term_to_string a in
                 let uu___5 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print4
                   "Computing %s.return for u_a:%s, a:%s, and e:%s{\n" uu___2
                   uu___3 uu___4 uu___5
               else ());
              (let uu___1 =
                 let uu___2 =
                   FStar_All.pipe_right ed
                     FStar_Syntax_Util.get_return_vc_combinator in
                 FStar_TypeChecker_Env.inst_tscheme_with uu___2 [u_a] in
               match uu___1 with
               | (uu___2, return_t) ->
                   let return_t_shape_error s =
                     let uu___3 =
                       let uu___4 =
                         FStar_Ident.string_of_lid
                           ed.FStar_Syntax_Syntax.mname in
                       let uu___5 =
                         FStar_Syntax_Print.term_to_string return_t in
                       FStar_Util.format3
                         "%s.return %s does not have proper shape (reason:%s)"
                         uu___4 uu___5 s in
                     (FStar_Errors.Fatal_UnexpectedEffect, uu___3) in
                   let uu___3 =
                     let uu___4 =
                       let uu___5 = FStar_Syntax_Subst.compress return_t in
                       uu___5.FStar_Syntax_Syntax.n in
                     match uu___4 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                         (FStar_List.length bs) >= (Prims.of_int (2)) ->
                         let uu___5 = FStar_Syntax_Subst.open_comp bs c in
                         (match uu___5 with
                          | (a_b::x_b::bs1, c1) ->
                              let uu___6 =
                                FStar_Syntax_Util.comp_to_comp_typ c1 in
                              (a_b, x_b, bs1, uu___6))
                     | uu___5 ->
                         let uu___6 =
                           return_t_shape_error
                             "Either not an arrow or not enough binders" in
                         FStar_Errors.raise_error uu___6 r in
                   (match uu___3 with
                    | (a_b, x_b, rest_bs, return_ct) ->
                        let uu___4 =
                          FStar_TypeChecker_Env.uvars_for_binders env rest_bs
                            [FStar_Syntax_Syntax.NT
                               ((a_b.FStar_Syntax_Syntax.binder_bv), a);
                            FStar_Syntax_Syntax.NT
                              ((x_b.FStar_Syntax_Syntax.binder_bv), e)]
                            (fun b ->
                               let uu___5 =
                                 FStar_Syntax_Print.binder_to_string b in
                               let uu___6 =
                                 let uu___7 =
                                   FStar_Ident.string_of_lid
                                     ed.FStar_Syntax_Syntax.mname in
                                 FStar_Util.format1 "%s.return" uu___7 in
                               let uu___7 = FStar_Range.string_of_range r in
                               FStar_Util.format3
                                 "implicit var for binder %s of %s at %s"
                                 uu___5 uu___6 uu___7) r in
                        (match uu___4 with
                         | (rest_bs_uvars, g_uvars) ->
                             let subst =
                               FStar_List.map2
                                 (fun b ->
                                    fun t ->
                                      FStar_Syntax_Syntax.NT
                                        ((b.FStar_Syntax_Syntax.binder_bv),
                                          t)) (a_b :: x_b :: rest_bs) (a :: e
                                 :: rest_bs_uvars) in
                             let is =
                               let uu___5 =
                                 let uu___6 =
                                   FStar_Syntax_Subst.compress
                                     return_ct.FStar_Syntax_Syntax.result_typ in
                                 let uu___7 = FStar_Syntax_Util.is_layered ed in
                                 effect_args_from_repr uu___6 uu___7 r in
                               FStar_All.pipe_right uu___5
                                 (FStar_List.map
                                    (FStar_Syntax_Subst.subst subst)) in
                             let c =
                               let uu___5 =
                                 let uu___6 =
                                   FStar_All.pipe_right is
                                     (FStar_List.map
                                        FStar_Syntax_Syntax.as_arg) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs = [u_a];
                                   FStar_Syntax_Syntax.effect_name =
                                     (ed.FStar_Syntax_Syntax.mname);
                                   FStar_Syntax_Syntax.result_typ = a;
                                   FStar_Syntax_Syntax.effect_args = uu___6;
                                   FStar_Syntax_Syntax.flags = []
                                 } in
                               FStar_Syntax_Syntax.mk_Comp uu___5 in
                             ((let uu___6 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffects") in
                               if uu___6
                               then
                                 let uu___7 =
                                   FStar_Syntax_Print.comp_to_string c in
                                 FStar_Util.print1 "} c after return %s\n"
                                   uu___7
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
              let uu___ =
                FStar_All.pipe_right ed FStar_Syntax_Util.is_layered in
              if uu___
              then mk_indexed_return env ed u_a a e r
              else
                (let uu___2 = mk_wp_return env ed u_a a e r in
                 (uu___2, FStar_TypeChecker_Env.trivial_guard))
let (lift_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp_typ ->
      FStar_TypeChecker_Env.mlift ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun c ->
      fun lift ->
        let uu___ =
          FStar_All.pipe_right
            (let uu___1 = c in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___1.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___1.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ =
                 (uu___1.FStar_Syntax_Syntax.result_typ);
               FStar_Syntax_Syntax.effect_args =
                 (uu___1.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags = []
             }) FStar_Syntax_Syntax.mk_Comp in
        FStar_All.pipe_right uu___ (lift.FStar_TypeChecker_Env.mlift_wp env)
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env ->
    fun l1_in ->
      fun l2_in ->
        let uu___ =
          let uu___1 = FStar_TypeChecker_Env.norm_eff_name env l1_in in
          let uu___2 = FStar_TypeChecker_Env.norm_eff_name env l2_in in
          (uu___1, uu___2) in
        match uu___ with
        | (l1, l2) ->
            let uu___1 = FStar_TypeChecker_Env.join_opt env l1 l2 in
            (match uu___1 with
             | FStar_Pervasives_Native.Some (m, uu___2, uu___3) -> m
             | FStar_Pervasives_Native.None ->
                 let uu___2 =
                   FStar_TypeChecker_Env.exists_polymonadic_bind env l1 l2 in
                 (match uu___2 with
                  | FStar_Pervasives_Native.Some (m, uu___3) -> m
                  | FStar_Pervasives_Native.None ->
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStar_Syntax_Print.lid_to_string l1_in in
                          let uu___6 = FStar_Syntax_Print.lid_to_string l2_in in
                          FStar_Util.format2
                            "Effects %s and %s cannot be composed" uu___5
                            uu___6 in
                        (FStar_Errors.Fatal_EffectsCannotBeComposed, uu___4) in
                      FStar_Errors.raise_error uu___3
                        env.FStar_TypeChecker_Env.range))
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env ->
    fun c1 ->
      fun c2 ->
        let uu___ =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2) in
        if uu___
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
            let uu___ =
              FStar_TypeChecker_Env.join_opt env
                c11.FStar_Syntax_Syntax.effect_name
                c21.FStar_Syntax_Syntax.effect_name in
            match uu___ with
            | FStar_Pervasives_Native.Some (m, lift1, lift2) ->
                let uu___1 = lift_comp env c11 lift1 in
                (match uu___1 with
                 | (c12, g1) ->
                     let uu___2 =
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
                          let uu___4 = lift_comp env_x c21 lift2 in
                          match uu___4 with
                          | (c22, g2) ->
                              let uu___5 =
                                FStar_TypeChecker_Env.close_guard env 
                                  [x_a] g2 in
                              (c22, uu___5)) in
                     (match uu___2 with | (c22, g2) -> (m, c12, c22, g1, g2)))
            | FStar_Pervasives_Native.None ->
                let uu___1 =
                  let uu___2 =
                    let uu___3 =
                      FStar_Syntax_Print.lid_to_string
                        c11.FStar_Syntax_Syntax.effect_name in
                    let uu___4 =
                      FStar_Syntax_Print.lid_to_string
                        c21.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2 "Effects %s and %s cannot be composed"
                      uu___3 uu___4 in
                  (FStar_Errors.Fatal_EffectsCannotBeComposed, uu___2) in
                FStar_Errors.raise_error uu___1
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
            let uu___ = lift_comps_sep_guards env c1 c2 b for_bind in
            match uu___ with
            | (l, c11, c21, g1, g2) ->
                let uu___1 = FStar_TypeChecker_Env.conj_guard g1 g2 in
                (l, c11, c21, uu___1)
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
          let uu___ =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid in
          if uu___
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_arrow uu___1 -> true
    | uu___1 -> false
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
              let uu___ =
                let uu___1 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu___1 in
              if uu___
              then f
              else (let uu___2 = reason1 () in label uu___2 r f)
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
            let uu___ = g in
            let uu___1 =
              let uu___2 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu___2 in
            {
              FStar_TypeChecker_Common.guard_f = uu___1;
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___.FStar_TypeChecker_Common.implicits)
            }
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun bvs ->
      fun c ->
        let uu___ = FStar_Syntax_Util.is_ml_comp c in
        if uu___
        then c
        else
          (let uu___2 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu___2
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close =
                  let uu___4 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator in
                  FStar_All.pipe_right uu___4 FStar_Util.must in
                FStar_List.fold_right
                  (fun x ->
                     fun wp ->
                       let bs =
                         let uu___4 = FStar_Syntax_Syntax.mk_binder x in
                         [uu___4] in
                       let us =
                         let uu___4 =
                           let uu___5 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu___5] in
                         u_res :: uu___4 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu___4 =
                         FStar_TypeChecker_Env.inst_effect_fun_with us env md
                           close in
                       let uu___5 =
                         let uu___6 = FStar_Syntax_Syntax.as_arg res_t in
                         let uu___7 =
                           let uu___8 =
                             FStar_Syntax_Syntax.as_arg
                               x.FStar_Syntax_Syntax.sort in
                           let uu___9 =
                             let uu___10 = FStar_Syntax_Syntax.as_arg wp1 in
                             [uu___10] in
                           uu___8 :: uu___9 in
                         uu___6 :: uu___7 in
                       FStar_Syntax_Syntax.mk_Tm_app uu___4 uu___5
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu___4 = destruct_wp_comp c1 in
              match uu___4 with
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
                let uu___ =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs) in
                FStar_All.pipe_right uu___
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
                  let uu___ =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs) in
                  FStar_All.pipe_right uu___
                    (close_guard_implicits env false bs)))
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___ ->
            match uu___ with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> true
            | uu___1 -> false))
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env ->
    fun eopt ->
      fun lc ->
        let lc_is_unit_or_effectful =
          let uu___ =
            let uu___1 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp in
            FStar_All.pipe_right uu___1 FStar_Pervasives_Native.snd in
          FStar_All.pipe_right uu___
            (fun c ->
               (let uu___1 =
                  (FStar_TypeChecker_Env.is_reifiable_comp env c) &&
                    (let uu___2 =
                       let uu___3 =
                         FStar_TypeChecker_Env.norm_eff_name env
                           lc.FStar_TypeChecker_Common.eff_name in
                       FStar_TypeChecker_Env.is_layered_effect env uu___3 in
                     Prims.op_Negation uu___2) in
                Prims.op_Negation uu___1) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu___1 = FStar_Syntax_Util.is_pure_or_ghost_comp c in
                     Prims.op_Negation uu___1))) in
        match eopt with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu___ = FStar_Syntax_Util.head_and_args_full e in
                match uu___ with
                | (head, uu___1) ->
                    let uu___2 =
                      let uu___3 = FStar_Syntax_Util.un_uinst head in
                      uu___3.FStar_Syntax_Syntax.n in
                    (match uu___2 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu___3 =
                           let uu___4 = FStar_Syntax_Syntax.lid_of_fv fv in
                           FStar_TypeChecker_Env.is_irreducible env uu___4 in
                         Prims.op_Negation uu___3
                     | uu___3 -> true)))
              &&
              (let uu___ = should_not_inline_lc lc in Prims.op_Negation uu___)
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
              | FStar_Pervasives_Native.Some u1 -> u1 in
            let uu___ = FStar_TypeChecker_Env.get_effect_decl env eff_lid in
            mk_return env uu___ u t v v.FStar_Syntax_Syntax.pos
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
                        let uu___ =
                          let uu___1 =
                            FStar_All.pipe_right m FStar_Ident.ident_of_lid in
                          FStar_All.pipe_right uu___1
                            FStar_Ident.string_of_id in
                        let uu___1 =
                          let uu___2 =
                            FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                          FStar_All.pipe_right uu___2
                            FStar_Ident.string_of_id in
                        let uu___2 =
                          let uu___3 =
                            FStar_All.pipe_right p FStar_Ident.ident_of_lid in
                          FStar_All.pipe_right uu___3
                            FStar_Ident.string_of_id in
                        FStar_Util.format3 "(%s, %s) |> %s" uu___ uu___1
                          uu___2 in
                      (let uu___1 =
                         (((FStar_TypeChecker_Env.is_erasable_effect env m)
                             &&
                             (let uu___2 =
                                FStar_TypeChecker_Env.is_erasable_effect env
                                  p in
                              Prims.op_Negation uu___2))
                            &&
                            (let uu___2 =
                               FStar_TypeChecker_Normalize.non_info_norm env
                                 ct1.FStar_Syntax_Syntax.result_typ in
                             Prims.op_Negation uu___2))
                           ||
                           (((FStar_TypeChecker_Env.is_erasable_effect env n)
                               &&
                               (let uu___2 =
                                  FStar_TypeChecker_Env.is_erasable_effect
                                    env p in
                                Prims.op_Negation uu___2))
                              &&
                              (let uu___2 =
                                 FStar_TypeChecker_Normalize.non_info_norm
                                   env ct2.FStar_Syntax_Syntax.result_typ in
                               Prims.op_Negation uu___2)) in
                       if uu___1
                       then
                         let uu___2 =
                           let uu___3 =
                             let uu___4 = FStar_Ident.string_of_lid p in
                             FStar_Util.format2
                               "Cannot apply bind %s since %s is not erasable and one of the computations is informative"
                               bind_name uu___4 in
                           (FStar_Errors.Fatal_UnexpectedEffect, uu___3) in
                         FStar_Errors.raise_error uu___2 r1
                       else ());
                      (let uu___2 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LayeredEffects") in
                       if uu___2
                       then
                         let uu___3 =
                           let uu___4 = FStar_Syntax_Syntax.mk_Comp ct1 in
                           FStar_Syntax_Print.comp_to_string uu___4 in
                         let uu___4 =
                           let uu___5 = FStar_Syntax_Syntax.mk_Comp ct2 in
                           FStar_Syntax_Print.comp_to_string uu___5 in
                         FStar_Util.print2 "Binding c1:%s and c2:%s {\n"
                           uu___3 uu___4
                       else ());
                      (let uu___3 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "ResolveImplicitsHook") in
                       if uu___3
                       then
                         let uu___4 =
                           let uu___5 = FStar_TypeChecker_Env.get_range env in
                           FStar_Range.string_of_range uu___5 in
                         let uu___5 =
                           FStar_Syntax_Print.tscheme_to_string bind_t in
                         FStar_Util.print2
                           "///////////////////////////////Bind at %s/////////////////////\nwith bind_t = %s\n"
                           uu___4 uu___5
                       else ());
                      (let uu___3 =
                         let uu___4 =
                           FStar_TypeChecker_Env.get_effect_decl env m in
                         let uu___5 =
                           FStar_TypeChecker_Env.get_effect_decl env n in
                         let uu___6 =
                           FStar_TypeChecker_Env.get_effect_decl env p in
                         (uu___4, uu___5, uu___6) in
                       match uu___3 with
                       | (m_ed, n_ed, p_ed) ->
                           let uu___4 =
                             let uu___5 =
                               FStar_List.hd
                                 ct1.FStar_Syntax_Syntax.comp_univs in
                             let uu___6 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 ct1.FStar_Syntax_Syntax.effect_args in
                             (uu___5, (ct1.FStar_Syntax_Syntax.result_typ),
                               uu___6) in
                           (match uu___4 with
                            | (u1, t1, is1) ->
                                let uu___5 =
                                  let uu___6 =
                                    FStar_List.hd
                                      ct2.FStar_Syntax_Syntax.comp_univs in
                                  let uu___7 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst
                                      ct2.FStar_Syntax_Syntax.effect_args in
                                  (uu___6,
                                    (ct2.FStar_Syntax_Syntax.result_typ),
                                    uu___7) in
                                (match uu___5 with
                                 | (u2, t2, is2) ->
                                     let uu___6 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         bind_t [u1; u2] in
                                     (match uu___6 with
                                      | (uu___7, bind_t1) ->
                                          let bind_t_shape_error s =
                                            let uu___8 =
                                              let uu___9 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t1 in
                                              FStar_Util.format3
                                                "bind %s (%s) does not have proper shape (reason:%s)"
                                                uu___9 bind_name s in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu___8) in
                                          let uu___8 =
                                            let uu___9 =
                                              let uu___10 =
                                                FStar_Syntax_Subst.compress
                                                  bind_t1 in
                                              uu___10.FStar_Syntax_Syntax.n in
                                            match uu___9 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs, c) when
                                                (FStar_List.length bs) >=
                                                  (Prims.of_int (4))
                                                ->
                                                let uu___10 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs c in
                                                (match uu___10 with
                                                 | (a_b::b_b::bs1, c1) ->
                                                     let uu___11 =
                                                       let uu___12 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2)))
                                                           bs1 in
                                                       FStar_All.pipe_right
                                                         uu___12
                                                         (fun uu___13 ->
                                                            match uu___13
                                                            with
                                                            | (l1, l2) ->
                                                                let uu___14 =
                                                                  FStar_List.hd
                                                                    l2 in
                                                                let uu___15 =
                                                                  let uu___16
                                                                    =
                                                                    FStar_List.tl
                                                                    l2 in
                                                                  FStar_List.hd
                                                                    uu___16 in
                                                                (l1, uu___14,
                                                                  uu___15)) in
                                                     (match uu___11 with
                                                      | (rest_bs, f_b, g_b)
                                                          ->
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b, c1)))
                                            | uu___10 ->
                                                let uu___11 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders" in
                                                FStar_Errors.raise_error
                                                  uu___11 r1 in
                                          (match uu___8 with
                                           | (a_b, b_b, rest_bs, f_b, g_b,
                                              bind_c) ->
                                               let uu___9 =
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs
                                                   [FStar_Syntax_Syntax.NT
                                                      ((a_b.FStar_Syntax_Syntax.binder_bv),
                                                        t1);
                                                   FStar_Syntax_Syntax.NT
                                                     ((b_b.FStar_Syntax_Syntax.binder_bv),
                                                       t2)]
                                                   (fun b1 ->
                                                      let uu___10 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1 in
                                                      let uu___11 =
                                                        FStar_Range.string_of_range
                                                          r1 in
                                                      FStar_Util.format3
                                                        "implicit var for binder %s of %s at %s"
                                                        uu___10 bind_name
                                                        uu___11) r1 in
                                               (match uu___9 with
                                                | (rest_bs_uvars, g_uvars) ->
                                                    ((let uu___11 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "ResolveImplicitsHook") in
                                                      if uu___11
                                                      then
                                                        FStar_All.pipe_right
                                                          rest_bs_uvars
                                                          (FStar_List.iter
                                                             (fun t ->
                                                                let uu___12 =
                                                                  let uu___13
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    t in
                                                                  uu___13.FStar_Syntax_Syntax.n in
                                                                match uu___12
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (u,
                                                                    uu___13)
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t in
                                                                    let uu___15
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
                                                                    uu___16
                                                                    ->
                                                                    "<no attr>" in
                                                                    FStar_Util.print2
                                                                    "Generated uvar %s with attribute %s\n"
                                                                    uu___14
                                                                    uu___15
                                                                | uu___13 ->
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t in
                                                                    Prims.op_Hat
                                                                    "Impossible, expected a uvar, got : "
                                                                    uu___15 in
                                                                    failwith
                                                                    uu___14))
                                                      else ());
                                                     (let subst =
                                                        FStar_List.map2
                                                          (fun b1 ->
                                                             fun t ->
                                                               FStar_Syntax_Syntax.NT
                                                                 ((b1.FStar_Syntax_Syntax.binder_bv),
                                                                   t)) (a_b
                                                          :: b_b :: rest_bs)
                                                          (t1 :: t2 ::
                                                          rest_bs_uvars) in
                                                      let f_guard =
                                                        let f_sort_is =
                                                          let uu___11 =
                                                            let uu___12 =
                                                              FStar_Syntax_Subst.compress
                                                                (f_b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                                            let uu___13 =
                                                              FStar_Syntax_Util.is_layered
                                                                m_ed in
                                                            effect_args_from_repr
                                                              uu___12 uu___13
                                                              r1 in
                                                          FStar_All.pipe_right
                                                            uu___11
                                                            (FStar_List.map
                                                               (FStar_Syntax_Subst.subst
                                                                  subst)) in
                                                        FStar_List.fold_left2
                                                          (fun g ->
                                                             fun i1 ->
                                                               fun f_i1 ->
                                                                 (let uu___12
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "ResolveImplicitsHook") in
                                                                  if uu___12
                                                                  then
                                                                    let uu___13
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    i1 in
                                                                    let uu___14
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    f_i1 in
                                                                    FStar_Util.print2
                                                                    "Generating constraint %s = %s\n"
                                                                    uu___13
                                                                    uu___14
                                                                  else ());
                                                                 (let uu___12
                                                                    =
                                                                    FStar_TypeChecker_Rel.layered_effect_teq
                                                                    env i1
                                                                    f_i1
                                                                    (FStar_Pervasives_Native.Some
                                                                    bind_name) in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g uu___12))
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
                                                          let uu___11 =
                                                            let uu___12 =
                                                              FStar_Syntax_Subst.compress
                                                                (g_b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                                            uu___12.FStar_Syntax_Syntax.n in
                                                          match uu___11 with
                                                          | FStar_Syntax_Syntax.Tm_arrow
                                                              (bs, c) ->
                                                              let uu___12 =
                                                                FStar_Syntax_Subst.open_comp
                                                                  bs c in
                                                              (match uu___12
                                                               with
                                                               | (bs1, c1) ->
                                                                   let bs_subst
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1 in
                                                                    uu___15.FStar_Syntax_Syntax.binder_bv in
                                                                    let uu___15
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a.FStar_Syntax_Syntax.binder_bv
                                                                    FStar_Syntax_Syntax.bv_to_name in
                                                                    (uu___14,
                                                                    uu___15) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu___13 in
                                                                   let c2 =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1 in
                                                                   let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2) in
                                                                    let uu___15
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed in
                                                                    effect_args_from_repr
                                                                    uu___14
                                                                    uu___15
                                                                    r1 in
                                                                   FStar_All.pipe_right
                                                                    uu___13
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst)))
                                                          | uu___12 ->
                                                              failwith
                                                                "impossible: mk_indexed_bind" in
                                                        let env_g =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env [x_a] in
                                                        let uu___11 =
                                                          FStar_List.fold_left2
                                                            (fun g ->
                                                               fun i1 ->
                                                                 fun g_i1 ->
                                                                   (let uu___13
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "ResolveImplicitsHook") in
                                                                    if
                                                                    uu___13
                                                                    then
                                                                    let uu___14
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    i1 in
                                                                    let uu___15
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    g_i1 in
                                                                    FStar_Util.print2
                                                                    "Generating constraint %s = %s\n"
                                                                    uu___14
                                                                    uu___15
                                                                    else ());
                                                                   (let uu___13
                                                                    =
                                                                    FStar_TypeChecker_Rel.layered_effect_teq
                                                                    env_g i1
                                                                    g_i1
                                                                    (FStar_Pervasives_Native.Some
                                                                    bind_name) in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g uu___13))
                                                            FStar_TypeChecker_Env.trivial_guard
                                                            is2 g_sort_is in
                                                        FStar_All.pipe_right
                                                          uu___11
                                                          (FStar_TypeChecker_Env.close_guard
                                                             env [x_a]) in
                                                      let bind_ct =
                                                        let uu___11 =
                                                          FStar_All.pipe_right
                                                            bind_c
                                                            (FStar_Syntax_Subst.subst_comp
                                                               subst) in
                                                        FStar_All.pipe_right
                                                          uu___11
                                                          FStar_Syntax_Util.comp_to_comp_typ in
                                                      let fml =
                                                        let uu___11 =
                                                          let uu___12 =
                                                            FStar_List.hd
                                                              bind_ct.FStar_Syntax_Syntax.comp_univs in
                                                          let uu___13 =
                                                            let uu___14 =
                                                              FStar_List.hd
                                                                bind_ct.FStar_Syntax_Syntax.effect_args in
                                                            FStar_Pervasives_Native.fst
                                                              uu___14 in
                                                          (uu___12, uu___13) in
                                                        match uu___11 with
                                                        | (u, wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              bind_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange in
                                                      let is =
                                                        let uu___11 =
                                                          FStar_Syntax_Subst.compress
                                                            bind_ct.FStar_Syntax_Syntax.result_typ in
                                                        let uu___12 =
                                                          FStar_Syntax_Util.is_layered
                                                            p_ed in
                                                        effect_args_from_repr
                                                          uu___11 uu___12 r1 in
                                                      let c =
                                                        let uu___11 =
                                                          let uu___12 =
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
                                                              = uu___12;
                                                            FStar_Syntax_Syntax.flags
                                                              = flags
                                                          } in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu___11 in
                                                      (let uu___12 =
                                                         FStar_All.pipe_left
                                                           (FStar_TypeChecker_Env.debug
                                                              env)
                                                           (FStar_Options.Other
                                                              "LayeredEffects") in
                                                       if uu___12
                                                       then
                                                         let uu___13 =
                                                           FStar_Syntax_Print.comp_to_string
                                                             c in
                                                         FStar_Util.print1
                                                           "} c after bind: %s\n"
                                                           uu___13
                                                       else ());
                                                      (let guard =
                                                         let uu___12 =
                                                           let uu___13 =
                                                             let uu___14 =
                                                               let uu___15 =
                                                                 let uu___16
                                                                   =
                                                                   FStar_TypeChecker_Env.guard_of_guard_formula
                                                                    (FStar_TypeChecker_Common.NonTrivial
                                                                    fml) in
                                                                 [uu___16] in
                                                               g_guard ::
                                                                 uu___15 in
                                                             f_guard ::
                                                               uu___14 in
                                                           g_uvars :: uu___13 in
                                                         FStar_TypeChecker_Env.conj_guards
                                                           uu___12 in
                                                       (let uu___13 =
                                                          FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "ResolveImplicitsHook") in
                                                        if uu___13
                                                        then
                                                          let uu___14 =
                                                            let uu___15 =
                                                              FStar_TypeChecker_Env.get_range
                                                                env in
                                                            FStar_Range.string_of_range
                                                              uu___15 in
                                                          let uu___15 =
                                                            FStar_TypeChecker_Rel.guard_to_string
                                                              env guard in
                                                          FStar_Util.print2
                                                            "///////////////////////////////EndBind at %s/////////////////////\nguard = %s\n"
                                                            uu___14 uu___15
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
                let uu___ =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m in
                  let uu___1 = FStar_TypeChecker_Env.wp_signature env m in
                  match uu___1 with
                  | (a, kwp) ->
                      let uu___2 = destruct_wp_comp ct1 in
                      let uu___3 = destruct_wp_comp ct2 in
                      ((md, a, kwp), uu___2, uu___3) in
                match uu___ with
                | ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None ->
                          let uu___1 = FStar_Syntax_Syntax.null_binder t1 in
                          [uu___1]
                      | FStar_Pervasives_Native.Some x ->
                          let uu___1 = FStar_Syntax_Syntax.mk_binder x in
                          [uu___1] in
                    let mk_lam wp =
                      FStar_Syntax_Util.abs bs wp
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.mk_residual_comp
                              FStar_Parser_Const.effect_Tot_lid
                              FStar_Pervasives_Native.None
                              [FStar_Syntax_Syntax.TOTAL])) in
                    let wp_args =
                      let uu___1 = FStar_Syntax_Syntax.as_arg t1 in
                      let uu___2 =
                        let uu___3 = FStar_Syntax_Syntax.as_arg t2 in
                        let uu___4 =
                          let uu___5 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu___6 =
                            let uu___7 =
                              let uu___8 = mk_lam wp2 in
                              FStar_Syntax_Syntax.as_arg uu___8 in
                            [uu___7] in
                          uu___5 :: uu___6 in
                        uu___3 :: uu___4 in
                      uu___1 :: uu___2 in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator in
                    let wp =
                      let uu___1 =
                        FStar_TypeChecker_Env.inst_effect_fun_with
                          [u_t1; u_t2] env md bind_wp in
                      FStar_Syntax_Syntax.mk_Tm_app uu___1 wp_args
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
              let uu___ =
                let uu___1 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1 in
                let uu___2 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2 in
                (uu___1, uu___2) in
              match uu___ with
              | (ct1, ct2) ->
                  let uu___1 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name in
                  (match uu___1 with
                   | FStar_Pervasives_Native.Some (p, f_bind) ->
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None ->
                       let uu___2 = lift_comps env c1 c2 b true in
                       (match uu___2 with
                        | (m, c11, c21, g_lift) ->
                            let uu___3 =
                              let uu___4 =
                                FStar_Syntax_Util.comp_to_comp_typ c11 in
                              let uu___5 =
                                FStar_Syntax_Util.comp_to_comp_typ c21 in
                              (uu___4, uu___5) in
                            (match uu___3 with
                             | (ct11, ct21) ->
                                 let uu___4 =
                                   let uu___5 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m in
                                   if uu___5
                                   then
                                     let bind_t =
                                       let uu___6 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env) in
                                       FStar_All.pipe_right uu___6
                                         FStar_Syntax_Util.get_bind_vc_combinator in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu___7 =
                                        mk_wp_bind env m ct11 b ct21 flags r1 in
                                      (uu___7,
                                        FStar_TypeChecker_Env.trivial_guard)) in
                                 (match uu___4 with
                                  | (c, g_bind) ->
                                      let uu___5 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind in
                                      (c, uu___5)))))
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
            let uu___ =
              let uu___1 =
                let uu___2 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg in
                [uu___2] in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu___1;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu___ in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags ->
    let uu___ =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1 ->
              match uu___1 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> true
              | uu___2 -> false)) in
    if uu___
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2 ->
              match uu___2 with
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
        let uu___ = FStar_Syntax_Util.is_ml_comp c in
        if uu___
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
           let pure_assume_wp =
             let uu___2 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None in
             FStar_Syntax_Syntax.fv_to_tm uu___2 in
           let pure_assume_wp1 =
             let uu___2 =
               let uu___3 =
                 FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula in
               [uu___3] in
             let uu___3 = FStar_TypeChecker_Env.get_range env in
             FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu___2 uu___3 in
           let uu___2 = weaken_flags ct.FStar_Syntax_Syntax.flags in
           bind_pure_wp_with env pure_assume_wp1 c uu___2)
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env ->
    fun lc ->
      fun f ->
        let weaken uu___ =
          let uu___1 = FStar_TypeChecker_Common.lcomp_comp lc in
          match uu___1 with
          | (c, g_c) ->
              let uu___2 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
              if uu___2
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu___4 = weaken_comp env c f1 in
                     (match uu___4 with
                      | (c1, g_w) ->
                          let uu___5 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w in
                          (c1, uu___5))) in
        let uu___ = weaken_flags lc.FStar_TypeChecker_Common.cflags in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu___ weaken
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
                 let uu___1 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None in
                 FStar_Syntax_Syntax.fv_to_tm uu___1 in
               let pure_assert_wp1 =
                 let uu___1 =
                   let uu___2 =
                     let uu___3 = label_opt env reason r f in
                     FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu___3 in
                   [uu___2] in
                 FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu___1 r in
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
            let uu___ = FStar_TypeChecker_Env.is_trivial_guard_formula g0 in
            if uu___
            then (lc, g0)
            else
              (let flags =
                 let uu___2 =
                   let uu___3 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc in
                   if uu___3
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, []) in
                 match uu___2 with
                 | (maybe_trivial_post, flags1) ->
                     let uu___3 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___4 ->
                               match uu___4 with
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
                               | uu___5 -> [])) in
                     FStar_List.append flags1 uu___3 in
               let strengthen uu___2 =
                 let uu___3 = FStar_TypeChecker_Common.lcomp_comp lc in
                 match uu___3 with
                 | (c, g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                        let uu___5 = FStar_TypeChecker_Env.guard_form g01 in
                        match uu___5 with
                        | FStar_TypeChecker_Common.Trivial -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu___7 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu___7
                              then
                                let uu___8 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only in
                                let uu___9 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu___8 uu___9
                              else ());
                             (let uu___7 =
                                strengthen_comp env reason c f flags in
                              match uu___7 with
                              | (c1, g_s) ->
                                  let uu___8 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s in
                                  (c1, uu___8)))) in
               let uu___2 =
                 let uu___3 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name in
                 FStar_TypeChecker_Common.mk_lcomp uu___3
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen in
               (uu___2,
                 (let uu___3 = g0 in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred_to_tac =
                      (uu___3.FStar_TypeChecker_Common.deferred_to_tac);
                    FStar_TypeChecker_Common.deferred =
                      (uu___3.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___3.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___3.FStar_TypeChecker_Common.implicits)
                  })))
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___ ->
            match uu___ with
            | FStar_Syntax_Syntax.SOMETRIVIAL -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION -> true
            | uu___1 -> false) lc.FStar_TypeChecker_Common.cflags)
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
          let uu___ =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax in
          if uu___
          then e
          else
            (let uu___2 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu___3 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid in
                  FStar_Option.isSome uu___3) in
             if uu___2
             then
               let u =
                 match uopt with
                 | FStar_Pervasives_Native.Some u1 -> u1
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
                | uu___ -> false in
              if is_unit
              then
                let uu___ =
                  let uu___1 =
                    let uu___2 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name in
                    FStar_All.pipe_right uu___2
                      (FStar_TypeChecker_Env.norm_eff_name env) in
                  FStar_All.pipe_right uu___1
                    (FStar_TypeChecker_Env.is_layered_effect env) in
                (if uu___
                 then
                   let uu___1 = FStar_Syntax_Subst.open_term_bv b phi in
                   match uu___1 with
                   | (b1, phi1) ->
                       let phi2 =
                         FStar_Syntax_Subst.subst
                           [FStar_Syntax_Syntax.NT
                              (b1, FStar_Syntax_Syntax.unit_const)] phi1 in
                       weaken_comp env c phi2
                 else
                   (let uu___2 = close_wp_comp env [x] c in
                    (uu___2, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu___ -> (c, FStar_TypeChecker_Env.trivial_guard)
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
          fun uu___ ->
            match uu___ with
            | (b, lc2) ->
                let debug f =
                  let uu___1 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu___1 then f () else () in
                let uu___1 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp2 env
                    (lc1, lc2) in
                (match uu___1 with
                 | (lc11, lc21) ->
                     let joined_eff = join_lcomp env lc11 lc21 in
                     let bind_flags =
                       let uu___2 =
                         (should_not_inline_lc lc11) ||
                           (should_not_inline_lc lc21) in
                       if uu___2
                       then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                       else
                         (let flags =
                            let uu___4 =
                              FStar_TypeChecker_Common.is_total_lcomp lc11 in
                            if uu___4
                            then
                              let uu___5 =
                                FStar_TypeChecker_Common.is_total_lcomp lc21 in
                              (if uu___5
                               then [FStar_Syntax_Syntax.TOTAL]
                               else
                                 (let uu___7 =
                                    FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                      lc21 in
                                  if uu___7
                                  then [FStar_Syntax_Syntax.SOMETRIVIAL]
                                  else []))
                            else
                              (let uu___6 =
                                 (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                    lc11)
                                   &&
                                   (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                      lc21) in
                               if uu___6
                               then [FStar_Syntax_Syntax.SOMETRIVIAL]
                               else []) in
                          let uu___4 = lcomp_has_trivial_postcondition lc21 in
                          if uu___4
                          then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION ::
                            flags
                          else flags) in
                     let bind_it uu___2 =
                       let uu___3 =
                         env.FStar_TypeChecker_Env.lax &&
                           (FStar_Options.ml_ish ()) in
                       if uu___3
                       then
                         let u_t =
                           env.FStar_TypeChecker_Env.universe_of env
                             lc21.FStar_TypeChecker_Common.res_typ in
                         let uu___4 =
                           lax_mk_tot_or_comp_l joined_eff u_t
                             lc21.FStar_TypeChecker_Common.res_typ [] in
                         (uu___4, FStar_TypeChecker_Env.trivial_guard)
                       else
                         (let uu___5 =
                            FStar_TypeChecker_Common.lcomp_comp lc11 in
                          match uu___5 with
                          | (c1, g_c1) ->
                              let uu___6 =
                                FStar_TypeChecker_Common.lcomp_comp lc21 in
                              (match uu___6 with
                               | (c2, g_c2) ->
                                   let trivial_guard =
                                     let uu___7 =
                                       match b with
                                       | FStar_Pervasives_Native.Some x ->
                                           let b1 =
                                             FStar_Syntax_Syntax.mk_binder x in
                                           let uu___8 =
                                             FStar_Syntax_Syntax.is_null_binder
                                               b1 in
                                           if uu___8
                                           then g_c2
                                           else
                                             FStar_TypeChecker_Env.close_guard
                                               env [b1] g_c2
                                       | FStar_Pervasives_Native.None -> g_c2 in
                                     FStar_TypeChecker_Env.conj_guard g_c1
                                       uu___7 in
                                   (debug
                                      (fun uu___8 ->
                                         let uu___9 =
                                           FStar_Syntax_Print.comp_to_string
                                             c1 in
                                         let uu___10 =
                                           match b with
                                           | FStar_Pervasives_Native.None ->
                                               "none"
                                           | FStar_Pervasives_Native.Some x
                                               ->
                                               FStar_Syntax_Print.bv_to_string
                                                 x in
                                         let uu___11 =
                                           FStar_Syntax_Print.comp_to_string
                                             c2 in
                                         FStar_Util.print3
                                           "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                           uu___9 uu___10 uu___11);
                                    (let aux uu___8 =
                                       let uu___9 =
                                         FStar_Syntax_Util.is_trivial_wp c1 in
                                       if uu___9
                                       then
                                         match b with
                                         | FStar_Pervasives_Native.None ->
                                             FStar_Pervasives.Inl
                                               (c2, "trivial no binder")
                                         | FStar_Pervasives_Native.Some
                                             uu___10 ->
                                             let uu___11 =
                                               FStar_Syntax_Util.is_ml_comp
                                                 c2 in
                                             (if uu___11
                                              then
                                                FStar_Pervasives.Inl
                                                  (c2, "trivial ml")
                                              else
                                                FStar_Pervasives.Inr
                                                  "c1 trivial; but c2 is not ML")
                                       else
                                         (let uu___11 =
                                            (FStar_Syntax_Util.is_ml_comp c1)
                                              &&
                                              (FStar_Syntax_Util.is_ml_comp
                                                 c2) in
                                          if uu___11
                                          then
                                            FStar_Pervasives.Inl
                                              (c2, "both ml")
                                          else
                                            FStar_Pervasives.Inr
                                              "c1 not trivial, and both are not ML") in
                                     let try_simplify uu___8 =
                                       let aux_with_trivial_guard uu___9 =
                                         let uu___10 = aux () in
                                         match uu___10 with
                                         | FStar_Pervasives.Inl (c, reason)
                                             ->
                                             FStar_Pervasives.Inl
                                               (c, trivial_guard, reason)
                                         | FStar_Pervasives.Inr reason ->
                                             FStar_Pervasives.Inr reason in
                                       let uu___9 =
                                         FStar_TypeChecker_Env.too_early_in_prims
                                           env in
                                       if uu___9
                                       then
                                         FStar_Pervasives.Inl
                                           (c2, trivial_guard,
                                             "Early in prims; we don't have bind yet")
                                       else
                                         (let uu___11 =
                                            FStar_Syntax_Util.is_total_comp
                                              c1 in
                                          if uu___11
                                          then
                                            let close_with_type_of_x x c =
                                              let x1 =
                                                let uu___12 = x in
                                                {
                                                  FStar_Syntax_Syntax.ppname
                                                    =
                                                    (uu___12.FStar_Syntax_Syntax.ppname);
                                                  FStar_Syntax_Syntax.index =
                                                    (uu___12.FStar_Syntax_Syntax.index);
                                                  FStar_Syntax_Syntax.sort =
                                                    (FStar_Syntax_Util.comp_result
                                                       c1)
                                                } in
                                              maybe_capture_unit_refinement
                                                env
                                                x1.FStar_Syntax_Syntax.sort
                                                x1 c in
                                            match (e1opt, b) with
                                            | (FStar_Pervasives_Native.Some
                                               e,
                                               FStar_Pervasives_Native.Some
                                               x) ->
                                                let uu___12 =
                                                  let uu___13 =
                                                    FStar_All.pipe_right c2
                                                      (FStar_Syntax_Subst.subst_comp
                                                         [FStar_Syntax_Syntax.NT
                                                            (x, e)]) in
                                                  FStar_All.pipe_right
                                                    uu___13
                                                    (close_with_type_of_x x) in
                                                (match uu___12 with
                                                 | (c21, g_close) ->
                                                     let uu___13 =
                                                       let uu___14 =
                                                         let uu___15 =
                                                           let uu___16 =
                                                             let uu___17 =
                                                               FStar_TypeChecker_Env.map_guard
                                                                 g_c2
                                                                 (FStar_Syntax_Subst.subst
                                                                    [
                                                                    FStar_Syntax_Syntax.NT
                                                                    (x, e)]) in
                                                             [uu___17;
                                                             g_close] in
                                                           g_c1 :: uu___16 in
                                                         FStar_TypeChecker_Env.conj_guards
                                                           uu___15 in
                                                       (c21, uu___14,
                                                         "c1 Tot") in
                                                     FStar_Pervasives.Inl
                                                       uu___13)
                                            | (uu___12,
                                               FStar_Pervasives_Native.Some
                                               x) ->
                                                let uu___13 =
                                                  FStar_All.pipe_right c2
                                                    (close_with_type_of_x x) in
                                                (match uu___13 with
                                                 | (c21, g_close) ->
                                                     let uu___14 =
                                                       let uu___15 =
                                                         let uu___16 =
                                                           let uu___17 =
                                                             let uu___18 =
                                                               let uu___19 =
                                                                 let uu___20
                                                                   =
                                                                   FStar_Syntax_Syntax.mk_binder
                                                                    x in
                                                                 [uu___20] in
                                                               FStar_TypeChecker_Env.close_guard
                                                                 env uu___19
                                                                 g_c2 in
                                                             [uu___18;
                                                             g_close] in
                                                           g_c1 :: uu___17 in
                                                         FStar_TypeChecker_Env.conj_guards
                                                           uu___16 in
                                                       (c21, uu___15,
                                                         "c1 Tot only close") in
                                                     FStar_Pervasives.Inl
                                                       uu___14)
                                            | (uu___12, uu___13) ->
                                                aux_with_trivial_guard ()
                                          else
                                            (let uu___13 =
                                               (FStar_Syntax_Util.is_tot_or_gtot_comp
                                                  c1)
                                                 &&
                                                 (FStar_Syntax_Util.is_tot_or_gtot_comp
                                                    c2) in
                                             if uu___13
                                             then
                                               let uu___14 =
                                                 let uu___15 =
                                                   FStar_Syntax_Syntax.mk_GTotal
                                                     (FStar_Syntax_Util.comp_result
                                                        c2) in
                                                 (uu___15, trivial_guard,
                                                   "both GTot") in
                                               FStar_Pervasives.Inl uu___14
                                             else aux_with_trivial_guard ())) in
                                     let uu___8 = try_simplify () in
                                     match uu___8 with
                                     | FStar_Pervasives.Inl (c, g, reason) ->
                                         (debug
                                            (fun uu___10 ->
                                               let uu___11 =
                                                 FStar_Syntax_Print.comp_to_string
                                                   c in
                                               FStar_Util.print2
                                                 "(2) bind: Simplified (because %s) to\n\t%s\n"
                                                 reason uu___11);
                                          (c, g))
                                     | FStar_Pervasives.Inr reason ->
                                         (debug
                                            (fun uu___10 ->
                                               FStar_Util.print1
                                                 "(2) bind: Not simplified because %s\n"
                                                 reason);
                                          (let mk_bind1 c11 b1 c21 g =
                                             let uu___10 =
                                               mk_bind env c11 b1 c21
                                                 bind_flags r1 in
                                             match uu___10 with
                                             | (c, g_bind) ->
                                                 let uu___11 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g g_bind in
                                                 (c, uu___11) in
                                           let mk_seq c11 b1 c21 =
                                             let c12 =
                                               FStar_TypeChecker_Env.unfold_effect_abbrev
                                                 env c11 in
                                             let c22 =
                                               FStar_TypeChecker_Env.unfold_effect_abbrev
                                                 env c21 in
                                             let uu___10 =
                                               FStar_TypeChecker_Env.join env
                                                 c12.FStar_Syntax_Syntax.effect_name
                                                 c22.FStar_Syntax_Syntax.effect_name in
                                             match uu___10 with
                                             | (m, uu___11, lift2) ->
                                                 let uu___12 =
                                                   lift_comp env c22 lift2 in
                                                 (match uu___12 with
                                                  | (c23, g2) ->
                                                      let uu___13 =
                                                        destruct_wp_comp c12 in
                                                      (match uu___13 with
                                                       | (u1, t1, wp1) ->
                                                           let md_pure_or_ghost
                                                             =
                                                             FStar_TypeChecker_Env.get_effect_decl
                                                               env
                                                               c12.FStar_Syntax_Syntax.effect_name in
                                                           let trivial =
                                                             let uu___14 =
                                                               FStar_All.pipe_right
                                                                 md_pure_or_ghost
                                                                 FStar_Syntax_Util.get_wp_trivial_combinator in
                                                             FStar_All.pipe_right
                                                               uu___14
                                                               FStar_Util.must in
                                                           let vc1 =
                                                             let uu___14 =
                                                               FStar_TypeChecker_Env.inst_effect_fun_with
                                                                 [u1] env
                                                                 md_pure_or_ghost
                                                                 trivial in
                                                             let uu___15 =
                                                               let uu___16 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   t1 in
                                                               let uu___17 =
                                                                 let uu___18
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    wp1 in
                                                                 [uu___18] in
                                                               uu___16 ::
                                                                 uu___17 in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               uu___14
                                                               uu___15 r1 in
                                                           let uu___14 =
                                                             strengthen_comp
                                                               env
                                                               FStar_Pervasives_Native.None
                                                               c23 vc1
                                                               bind_flags in
                                                           (match uu___14
                                                            with
                                                            | (c, g_s) ->
                                                                let uu___15 =
                                                                  FStar_TypeChecker_Env.conj_guards
                                                                    [g_c1;
                                                                    g_c2;
                                                                    g2;
                                                                    g_s] in
                                                                (c, uu___15)))) in
                                           let uu___10 =
                                             let t =
                                               FStar_Syntax_Util.comp_result
                                                 c1 in
                                             match comp_univ_opt c1 with
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 let uu___11 =
                                                   env.FStar_TypeChecker_Env.universe_of
                                                     env t in
                                                 (uu___11, t)
                                             | FStar_Pervasives_Native.Some u
                                                 -> (u, t) in
                                           match uu___10 with
                                           | (u_res_t1, res_t1) ->
                                               let uu___11 =
                                                 (FStar_Option.isSome b) &&
                                                   (should_return env e1opt
                                                      lc11) in
                                               if uu___11
                                               then
                                                 let e1 =
                                                   FStar_Option.get e1opt in
                                                 let x = FStar_Option.get b in
                                                 let uu___12 =
                                                   FStar_Syntax_Util.is_partial_return
                                                     c1 in
                                                 (if uu___12
                                                  then
                                                    (debug
                                                       (fun uu___14 ->
                                                          let uu___15 =
                                                            FStar_TypeChecker_Normalize.term_to_string
                                                              env e1 in
                                                          let uu___16 =
                                                            FStar_Syntax_Print.bv_to_string
                                                              x in
                                                          FStar_Util.print2
                                                            "(3) bind (case a): Substituting %s for %s"
                                                            uu___15 uu___16);
                                                     (let c21 =
                                                        FStar_Syntax_Subst.subst_comp
                                                          [FStar_Syntax_Syntax.NT
                                                             (x, e1)] c2 in
                                                      let g =
                                                        let uu___14 =
                                                          FStar_TypeChecker_Env.map_guard
                                                            g_c2
                                                            (FStar_Syntax_Subst.subst
                                                               [FStar_Syntax_Syntax.NT
                                                                  (x, e1)]) in
                                                        FStar_TypeChecker_Env.conj_guard
                                                          g_c1 uu___14 in
                                                      mk_bind1 c1 b c21 g))
                                                  else
                                                    (let uu___14 =
                                                       ((FStar_Options.vcgen_optimize_bind_as_seq
                                                           ())
                                                          &&
                                                          (lcomp_has_trivial_postcondition
                                                             lc11))
                                                         &&
                                                         (let uu___15 =
                                                            FStar_TypeChecker_Env.try_lookup_lid
                                                              env
                                                              FStar_Parser_Const.with_type_lid in
                                                          FStar_Option.isSome
                                                            uu___15) in
                                                     if uu___14
                                                     then
                                                       let e1' =
                                                         let uu___15 =
                                                           FStar_Options.vcgen_decorate_with_type
                                                             () in
                                                         if uu___15
                                                         then
                                                           FStar_Syntax_Util.mk_with_type
                                                             u_res_t1 res_t1
                                                             e1
                                                         else e1 in
                                                       (debug
                                                          (fun uu___16 ->
                                                             let uu___17 =
                                                               FStar_TypeChecker_Normalize.term_to_string
                                                                 env e1' in
                                                             let uu___18 =
                                                               FStar_Syntax_Print.bv_to_string
                                                                 x in
                                                             FStar_Util.print2
                                                               "(3) bind (case b): Substituting %s for %s"
                                                               uu___17
                                                               uu___18);
                                                        (let c21 =
                                                           FStar_Syntax_Subst.subst_comp
                                                             [FStar_Syntax_Syntax.NT
                                                                (x, e1')] c2 in
                                                         mk_seq c1 b c21))
                                                     else
                                                       (debug
                                                          (fun uu___17 ->
                                                             let uu___18 =
                                                               FStar_TypeChecker_Normalize.term_to_string
                                                                 env e1 in
                                                             let uu___19 =
                                                               FStar_Syntax_Print.bv_to_string
                                                                 x in
                                                             FStar_Util.print2
                                                               "(3) bind (case c): Adding equality %s = %s"
                                                               uu___18
                                                               uu___19);
                                                        (let c21 =
                                                           FStar_Syntax_Subst.subst_comp
                                                             [FStar_Syntax_Syntax.NT
                                                                (x, e1)] c2 in
                                                         let x_eq_e =
                                                           let uu___17 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_Syntax_Util.mk_eq2
                                                             u_res_t1 res_t1
                                                             e1 uu___17 in
                                                         let uu___17 =
                                                           let uu___18 =
                                                             let uu___19 =
                                                               let uu___20 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   x in
                                                               [uu___20] in
                                                             FStar_TypeChecker_Env.push_binders
                                                               env uu___19 in
                                                           weaken_comp
                                                             uu___18 c21
                                                             x_eq_e in
                                                         match uu___17 with
                                                         | (c22, g_w) ->
                                                             let g =
                                                               let uu___18 =
                                                                 let uu___19
                                                                   =
                                                                   let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x in
                                                                    [uu___22] in
                                                                    FStar_TypeChecker_Env.close_guard
                                                                    env
                                                                    uu___21
                                                                    g_w in
                                                                   let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x in
                                                                    [uu___24] in
                                                                    let uu___24
                                                                    =
                                                                    FStar_TypeChecker_Common.weaken_guard_formula
                                                                    g_c2
                                                                    x_eq_e in
                                                                    FStar_TypeChecker_Env.close_guard
                                                                    env
                                                                    uu___23
                                                                    uu___24 in
                                                                    [uu___22] in
                                                                   uu___20 ::
                                                                    uu___21 in
                                                                 g_c1 ::
                                                                   uu___19 in
                                                               FStar_TypeChecker_Env.conj_guards
                                                                 uu___18 in
                                                             mk_bind1 c1 b
                                                               c22 g))))
                                               else
                                                 mk_bind1 c1 b c2
                                                   trivial_guard)))))) in
                     FStar_TypeChecker_Common.mk_lcomp joined_eff
                       lc21.FStar_TypeChecker_Common.res_typ bind_flags
                       bind_it)
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
      | uu___ -> g2
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
            let uu___ =
              (FStar_All.pipe_right m_opt FStar_Util.is_none) ||
                (is_ghost_effect env lc.FStar_TypeChecker_Common.eff_name) in
            if uu___
            then FStar_Parser_Const.effect_PURE_lid
            else FStar_All.pipe_right m_opt FStar_Util.must in
          let flags =
            let uu___ = FStar_TypeChecker_Common.is_total_lcomp lc in
            if uu___
            then FStar_Syntax_Syntax.RETURN ::
              (lc.FStar_TypeChecker_Common.cflags)
            else FStar_Syntax_Syntax.PARTIAL_RETURN ::
              (lc.FStar_TypeChecker_Common.cflags) in
          let refine uu___ =
            let uu___1 = FStar_TypeChecker_Common.lcomp_comp lc in
            match uu___1 with
            | (c, g_c) ->
                let u_t =
                  match comp_univ_opt c with
                  | FStar_Pervasives_Native.Some u_t1 -> u_t1
                  | FStar_Pervasives_Native.None ->
                      env.FStar_TypeChecker_Env.universe_of env
                        (FStar_Syntax_Util.comp_result c) in
                let uu___2 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu___2
                then
                  let uu___3 =
                    return_value env m (FStar_Pervasives_Native.Some u_t)
                      (FStar_Syntax_Util.comp_result c) e in
                  (match uu___3 with
                   | (retc, g_retc) ->
                       let g_c1 = FStar_TypeChecker_Env.conj_guard g_c g_retc in
                       let uu___4 =
                         let uu___5 = FStar_Syntax_Util.is_pure_comp c in
                         Prims.op_Negation uu___5 in
                       if uu___4
                       then
                         let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                         let retc2 =
                           let uu___5 = retc1 in
                           {
                             FStar_Syntax_Syntax.comp_univs =
                               (uu___5.FStar_Syntax_Syntax.comp_univs);
                             FStar_Syntax_Syntax.effect_name =
                               FStar_Parser_Const.effect_GHOST_lid;
                             FStar_Syntax_Syntax.result_typ =
                               (uu___5.FStar_Syntax_Syntax.result_typ);
                             FStar_Syntax_Syntax.effect_args =
                               (uu___5.FStar_Syntax_Syntax.effect_args);
                             FStar_Syntax_Syntax.flags = flags
                           } in
                         let uu___5 = FStar_Syntax_Syntax.mk_Comp retc2 in
                         (uu___5, g_c1)
                       else
                         (let uu___6 =
                            FStar_Syntax_Util.comp_set_flags retc flags in
                          (uu___6, g_c1)))
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
                   let uu___4 =
                     return_value env_x m (FStar_Pervasives_Native.Some u_t)
                       t xexp in
                   match uu___4 with
                   | (ret, g_ret) ->
                       let ret1 =
                         let uu___5 =
                           FStar_Syntax_Util.comp_set_flags ret
                             [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                         FStar_All.pipe_left
                           FStar_TypeChecker_Common.lcomp_of_comp uu___5 in
                       let eq = FStar_Syntax_Util.mk_eq2 u_t t xexp e in
                       let eq_ret =
                         weaken_precondition env_x ret1
                           (FStar_TypeChecker_Common.NonTrivial eq) in
                       let uu___5 =
                         let uu___6 =
                           let uu___7 =
                             FStar_TypeChecker_Common.lcomp_of_comp c2 in
                           bind e.FStar_Syntax_Syntax.pos env
                             FStar_Pervasives_Native.None uu___7
                             ((FStar_Pervasives_Native.Some x), eq_ret) in
                         FStar_TypeChecker_Common.lcomp_comp uu___6 in
                       (match uu___5 with
                        | (bind_c, g_bind) ->
                            let uu___6 =
                              FStar_Syntax_Util.comp_set_flags bind_c flags in
                            let uu___7 =
                              FStar_TypeChecker_Env.conj_guards
                                [g_c; g_ret; g_bind] in
                            (uu___6, uu___7))) in
          let uu___ = should_not_inline_lc lc in
          if uu___
          then
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format1
                  "assume_result_eq_pure_term cannot inline an non-inlineable lc : %s"
                  uu___3 in
              (FStar_Errors.Fatal_UnexpectedTerm, uu___2) in
            FStar_Errors.raise_error uu___1 e.FStar_Syntax_Syntax.pos
          else
            (let uu___2 = refine () in
             match uu___2 with
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
                (let uu___ = FStar_TypeChecker_Env.too_early_in_prims env in
                 Prims.op_Negation uu___))
               && (should_return env (FStar_Pervasives_Native.Some e) lc))
              &&
              (let uu___ =
                 FStar_TypeChecker_Common.is_lcomp_partial_return lc in
               Prims.op_Negation uu___) in
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
            fun uu___ ->
              match uu___ with
              | (x, lc2) ->
                  let env_x =
                    match x with
                    | FStar_Pervasives_Native.None -> env
                    | FStar_Pervasives_Native.Some x1 ->
                        FStar_TypeChecker_Env.push_bv env x1 in
                  let uu___1 =
                    FStar_TypeChecker_Normalize.ghost_to_pure_lcomp2 env
                      (lc1, lc2) in
                  (match uu___1 with
                   | (lc11, lc21) ->
                       let lc22 =
                         let eff1 =
                           FStar_TypeChecker_Env.norm_eff_name env
                             lc11.FStar_TypeChecker_Common.eff_name in
                         let eff2 =
                           FStar_TypeChecker_Env.norm_eff_name env
                             lc21.FStar_TypeChecker_Common.eff_name in
                         let uu___2 =
                           ((FStar_Ident.lid_equals eff2
                               FStar_Parser_Const.effect_PURE_lid)
                              &&
                              (let uu___3 =
                                 FStar_TypeChecker_Env.join_opt env eff1 eff2 in
                               FStar_All.pipe_right uu___3 FStar_Util.is_none))
                             &&
                             (let uu___3 =
                                FStar_TypeChecker_Env.exists_polymonadic_bind
                                  env eff1 eff2 in
                              FStar_All.pipe_right uu___3 FStar_Util.is_none) in
                         if uu___2
                         then
                           let uu___3 =
                             FStar_All.pipe_right eff1
                               (fun uu___4 ->
                                  FStar_Pervasives_Native.Some uu___4) in
                           assume_result_eq_pure_term_in_m env_x uu___3 e2
                             lc21
                         else
                           (let uu___4 =
                              ((let uu___5 = is_pure_or_ghost_effect env eff1 in
                                Prims.op_Negation uu___5) ||
                                 (should_not_inline_lc lc11))
                                && (is_pure_or_ghost_effect env eff2) in
                            if uu___4
                            then
                              let uu___5 =
                                FStar_All.pipe_right eff1
                                  (fun uu___6 ->
                                     FStar_Pervasives_Native.Some uu___6) in
                              maybe_assume_result_eq_pure_term_in_m env_x
                                uu___5 e2 lc21
                            else lc21) in
                       bind r env e1opt lc11 (x, lc22))
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun lid ->
      let uu___ =
        let uu___1 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu___1 in
      FStar_Syntax_Syntax.fvar uu___ FStar_Syntax_Syntax.delta_constant
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
                    let uu___ =
                      FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                    FStar_Util.format1 "%s.conjunction" uu___ in
                  let uu___ =
                    let uu___1 =
                      let uu___2 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator in
                      FStar_All.pipe_right uu___2 FStar_Util.must in
                    FStar_TypeChecker_Env.inst_tscheme_with uu___1 [u_a] in
                  match uu___ with
                  | (uu___1, conjunction) ->
                      let uu___2 =
                        let uu___3 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args in
                        let uu___4 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args in
                        (uu___3, uu___4) in
                      (match uu___2 with
                       | (is1, is2) ->
                           let conjunction_t_error s =
                             let uu___3 =
                               let uu___4 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction in
                               FStar_Util.format3
                                 "conjunction %s (%s) does not have proper shape (reason:%s)"
                                 uu___4 conjunction_name s in
                             (FStar_Errors.Fatal_UnexpectedEffect, uu___3) in
                           let uu___3 =
                             let uu___4 =
                               let uu___5 =
                                 FStar_Syntax_Subst.compress conjunction in
                               uu___5.FStar_Syntax_Syntax.n in
                             match uu___4 with
                             | FStar_Syntax_Syntax.Tm_abs (bs, body, uu___5)
                                 when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu___6 =
                                   FStar_Syntax_Subst.open_term bs body in
                                 (match uu___6 with
                                  | (a_b::bs1, body1) ->
                                      let uu___7 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1 in
                                      (match uu___7 with
                                       | (rest_bs, f_b::g_b::p_b::[]) ->
                                           let uu___8 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu___8)))
                             | uu___5 ->
                                 let uu___6 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders" in
                                 FStar_Errors.raise_error uu___6 r in
                           (match uu___3 with
                            | (a_b, rest_bs, f_b, g_b, p_b, body) ->
                                let uu___4 =
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs
                                    [FStar_Syntax_Syntax.NT
                                       ((a_b.FStar_Syntax_Syntax.binder_bv),
                                         a)]
                                    (fun b ->
                                       let uu___5 =
                                         FStar_Syntax_Print.binder_to_string
                                           b in
                                       let uu___6 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname in
                                       let uu___7 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu___5 uu___6 uu___7) r in
                                (match uu___4 with
                                 | (rest_bs_uvars, g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b ->
                                            fun t ->
                                              FStar_Syntax_Syntax.NT
                                                ((b.FStar_Syntax_Syntax.binder_bv),
                                                  t)) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p])) in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu___5 =
                                           let uu___6 =
                                             FStar_Syntax_Subst.compress
                                               (f_b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                           uu___6.FStar_Syntax_Syntax.n in
                                         match uu___5 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu___6, uu___7::is) ->
                                             let uu___8 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst) in
                                             FStar_All.pipe_right uu___8
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu___6 ->
                                             let uu___7 =
                                               conjunction_t_error
                                                 "f's type is not a repr type" in
                                             FStar_Errors.raise_error uu___7
                                               r in
                                       FStar_List.fold_left2
                                         (fun g ->
                                            fun i1 ->
                                              fun f_i ->
                                                let uu___5 =
                                                  FStar_TypeChecker_Rel.layered_effect_teq
                                                    env i1 f_i
                                                    (FStar_Pervasives_Native.Some
                                                       conjunction_name) in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu___5)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu___5 =
                                           let uu___6 =
                                             FStar_Syntax_Subst.compress
                                               (g_b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                           uu___6.FStar_Syntax_Syntax.n in
                                         match uu___5 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu___6, uu___7::is) ->
                                             let uu___8 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst) in
                                             FStar_All.pipe_right uu___8
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu___6 ->
                                             let uu___7 =
                                               conjunction_t_error
                                                 "g's type is not a repr type" in
                                             FStar_Errors.raise_error uu___7
                                               r in
                                       FStar_List.fold_left2
                                         (fun g ->
                                            fun i2 ->
                                              fun g_i ->
                                                let uu___5 =
                                                  FStar_TypeChecker_Rel.layered_effect_teq
                                                    env i2 g_i
                                                    (FStar_Pervasives_Native.Some
                                                       conjunction_name) in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu___5)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body in
                                     let is =
                                       let uu___5 =
                                         let uu___6 =
                                           FStar_Syntax_Subst.compress body1 in
                                         uu___6.FStar_Syntax_Syntax.n in
                                       match uu___5 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu___6, a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu___6 ->
                                           let uu___7 =
                                             conjunction_t_error
                                               "body is not a repr type" in
                                           FStar_Errors.raise_error uu___7 r in
                                     let uu___5 =
                                       let uu___6 =
                                         let uu___7 =
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
                                             uu___7;
                                           FStar_Syntax_Syntax.flags = []
                                         } in
                                       FStar_Syntax_Syntax.mk_Comp uu___6 in
                                     let uu___6 =
                                       let uu___7 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu___7 g_guard in
                                     (uu___5, uu___6))))
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
                fun uu___ ->
                  let p1 = FStar_Syntax_Util.b2t p in
                  let if_then_else =
                    let uu___1 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator in
                    FStar_All.pipe_right uu___1 FStar_Util.must in
                  let uu___1 = destruct_wp_comp ct1 in
                  match uu___1 with
                  | (uu___2, uu___3, wp_t) ->
                      let uu___4 = destruct_wp_comp ct2 in
                      (match uu___4 with
                       | (uu___5, uu___6, wp_e) ->
                           let wp =
                             let uu___7 =
                               FStar_TypeChecker_Env.inst_effect_fun_with
                                 [u_a] env ed if_then_else in
                             let uu___8 =
                               let uu___9 = FStar_Syntax_Syntax.as_arg a in
                               let uu___10 =
                                 let uu___11 = FStar_Syntax_Syntax.as_arg p1 in
                                 let uu___12 =
                                   let uu___13 =
                                     FStar_Syntax_Syntax.as_arg wp_t in
                                   let uu___14 =
                                     let uu___15 =
                                       FStar_Syntax_Syntax.as_arg wp_e in
                                     [uu___15] in
                                   uu___13 :: uu___14 in
                                 uu___11 :: uu___12 in
                               uu___9 :: uu___10 in
                             let uu___9 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Syntax.mk_Tm_app uu___7 uu___8
                               uu___9 in
                           let uu___7 = mk_comp ed u_a a wp [] in
                           (uu___7, FStar_TypeChecker_Env.trivial_guard))
let (comp_pure_wp_false :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun u ->
      fun t ->
        let post_k =
          let uu___ =
            let uu___1 = FStar_Syntax_Syntax.null_binder t in [uu___1] in
          let uu___1 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
          FStar_Syntax_Util.arrow uu___ uu___1 in
        let kwp =
          let uu___ =
            let uu___1 = FStar_Syntax_Syntax.null_binder post_k in [uu___1] in
          let uu___1 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
          FStar_Syntax_Util.arrow uu___ uu___1 in
        let post =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k in
        let wp =
          let uu___ =
            let uu___1 = FStar_Syntax_Syntax.mk_binder post in [uu___1] in
          let uu___1 = fvar_const env FStar_Parser_Const.false_lid in
          FStar_Syntax_Util.abs uu___ uu___1
            (FStar_Pervasives_Native.Some
               (FStar_Syntax_Util.mk_residual_comp
                  FStar_Parser_Const.effect_Tot_lid
                  FStar_Pervasives_Native.None [FStar_Syntax_Syntax.TOTAL])) in
        let md =
          FStar_TypeChecker_Env.get_effect_decl env
            FStar_Parser_Const.effect_PURE_lid in
        mk_comp md u t wp []
let (get_neg_branch_conds :
  FStar_Syntax_Syntax.formula Prims.list ->
    (FStar_Syntax_Syntax.formula Prims.list * FStar_Syntax_Syntax.formula))
  =
  fun branch_conds ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStar_All.pipe_right branch_conds
            (FStar_List.fold_left
               (fun uu___3 ->
                  fun g ->
                    match uu___3 with
                    | (conds, acc) ->
                        let cond =
                          let uu___4 =
                            let uu___5 =
                              FStar_All.pipe_right g FStar_Syntax_Util.b2t in
                            FStar_All.pipe_right uu___5
                              FStar_Syntax_Util.mk_neg in
                          FStar_Syntax_Util.mk_conj acc uu___4 in
                        ((FStar_List.append conds [cond]), cond))
               ([FStar_Syntax_Util.t_true], FStar_Syntax_Util.t_true)) in
        FStar_All.pipe_right uu___2 FStar_Pervasives_Native.fst in
      FStar_All.pipe_right uu___1
        (fun l ->
           FStar_List.splitAt ((FStar_List.length l) - Prims.int_one) l) in
    FStar_All.pipe_right uu___
      (fun uu___1 ->
         match uu___1 with
         | (l1, l2) -> let uu___2 = FStar_List.hd l2 in (l1, uu___2))
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
            let uu___ =
              let uu___1 =
                FStar_All.pipe_right scrutinee FStar_Syntax_Syntax.mk_binder in
              [uu___1] in
            FStar_TypeChecker_Env.push_binders env0 uu___ in
          let eff =
            FStar_List.fold_left
              (fun eff1 ->
                 fun uu___ ->
                   match uu___ with
                   | (uu___1, eff_label, uu___2, uu___3) ->
                       join_effects env eff1 eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases in
          let uu___ =
            let uu___1 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu___2 ->
                      match uu___2 with
                      | (uu___3, uu___4, flags, uu___5) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___6 ->
                                  match uu___6 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE ->
                                      true
                                  | uu___7 -> false)))) in
            if uu___1
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, []) in
          match uu___ with
          | (should_not_inline_whole_match, bind_cases_flags) ->
              let bind_cases1 uu___1 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
                let uu___2 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
                if uu___2
                then
                  let uu___3 = lax_mk_tot_or_comp_l eff u_res_t res_t [] in
                  (uu___3, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let maybe_return eff_label_then cthen =
                     let uu___4 =
                       should_not_inline_whole_match ||
                         (let uu___5 = is_pure_or_ghost_effect env eff in
                          Prims.op_Negation uu___5) in
                     if uu___4 then cthen true else cthen false in
                   let uu___4 =
                     let uu___5 =
                       FStar_All.pipe_right lcases
                         (FStar_List.map
                            (fun uu___6 ->
                               match uu___6 with
                               | (g, uu___7, uu___8, uu___9) -> g)) in
                     get_neg_branch_conds uu___5 in
                   match uu___4 with
                   | (neg_branch_conds, exhaustiveness_branch_cond) ->
                       let uu___5 =
                         match lcases with
                         | [] ->
                             let uu___6 =
                               comp_pure_wp_false env u_res_t res_t in
                             (FStar_Pervasives_Native.None, uu___6,
                               FStar_TypeChecker_Env.trivial_guard)
                         | uu___6 ->
                             let uu___7 =
                               let uu___8 =
                                 let uu___9 =
                                   FStar_All.pipe_right neg_branch_conds
                                     (FStar_List.splitAt
                                        ((FStar_List.length lcases) -
                                           Prims.int_one)) in
                                 FStar_All.pipe_right uu___9
                                   (fun uu___10 ->
                                      match uu___10 with
                                      | (l1, l2) ->
                                          let uu___11 = FStar_List.hd l2 in
                                          (l1, uu___11)) in
                               match uu___8 with
                               | (neg_branch_conds1, neg_last) ->
                                   let uu___9 =
                                     let uu___10 =
                                       FStar_All.pipe_right lcases
                                         (FStar_List.splitAt
                                            ((FStar_List.length lcases) -
                                               Prims.int_one)) in
                                     FStar_All.pipe_right uu___10
                                       (fun uu___11 ->
                                          match uu___11 with
                                          | (l1, l2) ->
                                              let uu___12 = FStar_List.hd l2 in
                                              (l1, uu___12)) in
                                   (match uu___9 with
                                    | (lcases1,
                                       (g_last, eff_last, uu___10, c_last))
                                        ->
                                        let uu___11 =
                                          let lc =
                                            maybe_return eff_last c_last in
                                          let uu___12 =
                                            FStar_TypeChecker_Common.lcomp_comp
                                              lc in
                                          match uu___12 with
                                          | (c, g) ->
                                              let uu___13 =
                                                let uu___14 =
                                                  let uu___15 =
                                                    FStar_Syntax_Util.b2t
                                                      g_last in
                                                  FStar_Syntax_Util.mk_conj
                                                    uu___15 neg_last in
                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                  g uu___14 in
                                              (c, uu___13) in
                                        (match uu___11 with
                                         | (c, g) ->
                                             let uu___12 =
                                               let uu___13 =
                                                 FStar_All.pipe_right
                                                   eff_last
                                                   (FStar_TypeChecker_Env.norm_eff_name
                                                      env) in
                                               FStar_All.pipe_right uu___13
                                                 (FStar_TypeChecker_Env.get_effect_decl
                                                    env) in
                                             (lcases1, neg_branch_conds1,
                                               uu___12, c, g))) in
                             (match uu___7 with
                              | (lcases1, neg_branch_conds1, md, comp,
                                 g_comp) ->
                                  FStar_List.fold_right2
                                    (fun uu___8 ->
                                       fun neg_cond ->
                                         fun uu___9 ->
                                           match (uu___8, uu___9) with
                                           | ((g, eff_label, uu___10, cthen),
                                              (uu___11, celse, g_comp1)) ->
                                               let uu___12 =
                                                 let uu___13 =
                                                   maybe_return eff_label
                                                     cthen in
                                                 FStar_TypeChecker_Common.lcomp_comp
                                                   uu___13 in
                                               (match uu___12 with
                                                | (cthen1, g_then) ->
                                                    let uu___13 =
                                                      let uu___14 =
                                                        lift_comps_sep_guards
                                                          env cthen1 celse
                                                          FStar_Pervasives_Native.None
                                                          false in
                                                      match uu___14 with
                                                      | (m, cthen2, celse1,
                                                         g_lift_then,
                                                         g_lift_else) ->
                                                          let md1 =
                                                            FStar_TypeChecker_Env.get_effect_decl
                                                              env m in
                                                          let uu___15 =
                                                            FStar_All.pipe_right
                                                              cthen2
                                                              FStar_Syntax_Util.comp_to_comp_typ in
                                                          let uu___16 =
                                                            FStar_All.pipe_right
                                                              celse1
                                                              FStar_Syntax_Util.comp_to_comp_typ in
                                                          (md1, uu___15,
                                                            uu___16,
                                                            g_lift_then,
                                                            g_lift_else) in
                                                    (match uu___13 with
                                                     | (md1, ct_then,
                                                        ct_else, g_lift_then,
                                                        g_lift_else) ->
                                                         let fn =
                                                           let uu___14 =
                                                             FStar_All.pipe_right
                                                               md1
                                                               FStar_Syntax_Util.is_layered in
                                                           if uu___14
                                                           then
                                                             mk_layered_conjunction
                                                           else
                                                             mk_non_layered_conjunction in
                                                         let uu___14 =
                                                           let uu___15 =
                                                             FStar_TypeChecker_Env.get_range
                                                               env in
                                                           fn env md1 u_res_t
                                                             res_t g ct_then
                                                             ct_else uu___15 in
                                                         (match uu___14 with
                                                          | (c,
                                                             g_conjunction)
                                                              ->
                                                              let uu___15 =
                                                                let g1 =
                                                                  FStar_Syntax_Util.b2t
                                                                    g in
                                                                let uu___16 =
                                                                  let uu___17
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_then
                                                                    g_lift_then in
                                                                  let uu___18
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    g1 in
                                                                  FStar_TypeChecker_Common.weaken_guard_formula
                                                                    uu___17
                                                                    uu___18 in
                                                                let uu___17 =
                                                                  let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    FStar_Syntax_Util.mk_neg
                                                                    g1 in
                                                                    FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    uu___19 in
                                                                  FStar_TypeChecker_Common.weaken_guard_formula
                                                                    g_lift_else
                                                                    uu___18 in
                                                                (uu___16,
                                                                  uu___17) in
                                                              (match uu___15
                                                               with
                                                               | (g_then1,
                                                                  g_else) ->
                                                                   let uu___16
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guards
                                                                    [g_comp1;
                                                                    g_then1;
                                                                    g_else;
                                                                    g_conjunction] in
                                                                   ((FStar_Pervasives_Native.Some
                                                                    md1), c,
                                                                    uu___16))))))
                                    lcases1 neg_branch_conds1
                                    ((FStar_Pervasives_Native.Some md), comp,
                                      g_comp)) in
                       (match uu___5 with
                        | (md, comp, g_comp) ->
                            let uu___6 =
                              let uu___7 =
                                let check =
                                  FStar_Syntax_Util.mk_imp
                                    exhaustiveness_branch_cond
                                    FStar_Syntax_Util.t_false in
                                let check1 =
                                  let uu___8 =
                                    FStar_TypeChecker_Env.get_range env in
                                  label
                                    FStar_TypeChecker_Err.exhaustiveness_check
                                    uu___8 check in
                                strengthen_comp env
                                  FStar_Pervasives_Native.None comp check1
                                  bind_cases_flags in
                              match uu___7 with
                              | (c, g) ->
                                  let uu___8 =
                                    FStar_TypeChecker_Env.conj_guard g_comp g in
                                  (c, uu___8) in
                            (match uu___6 with
                             | (comp1, g_comp1) ->
                                 (match lcases with
                                  | [] -> (comp1, g_comp1)
                                  | uu___7::[] -> (comp1, g_comp1)
                                  | uu___7 ->
                                      let uu___8 =
                                        let uu___9 =
                                          FStar_All.pipe_right md
                                            FStar_Util.must in
                                        FStar_All.pipe_right uu___9
                                          FStar_Syntax_Util.is_layered in
                                      if uu___8
                                      then (comp1, g_comp1)
                                      else
                                        (let comp2 =
                                           FStar_TypeChecker_Env.comp_to_comp_typ
                                             env comp1 in
                                         let md1 =
                                           FStar_TypeChecker_Env.get_effect_decl
                                             env
                                             comp2.FStar_Syntax_Syntax.effect_name in
                                         let uu___10 = destruct_wp_comp comp2 in
                                         match uu___10 with
                                         | (uu___11, uu___12, wp) ->
                                             let ite_wp =
                                               let uu___13 =
                                                 FStar_All.pipe_right md1
                                                   FStar_Syntax_Util.get_wp_ite_combinator in
                                               FStar_All.pipe_right uu___13
                                                 FStar_Util.must in
                                             let wp1 =
                                               let uu___13 =
                                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                                   [u_res_t] env md1 ite_wp in
                                               let uu___14 =
                                                 let uu___15 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     res_t in
                                                 let uu___16 =
                                                   let uu___17 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp in
                                                   [uu___17] in
                                                 uu___15 :: uu___16 in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu___13 uu___14
                                                 wp.FStar_Syntax_Syntax.pos in
                                             let uu___13 =
                                               mk_comp md1 u_res_t res_t wp1
                                                 bind_cases_flags in
                                             (uu___13, g_comp1)))))) in
              FStar_TypeChecker_Common.mk_lcomp eff res_t bind_cases_flags
                bind_cases1
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
          let uu___1 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu___1 with
          | FStar_Pervasives_Native.None ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu___2 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c' in
                let uu___3 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error uu___2 uu___3
              else
                (let uu___3 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c' in
                 let uu___4 = FStar_TypeChecker_Env.get_range env in
                 FStar_Errors.raise_error uu___3 uu___4)
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
          let uu___ =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name in
          FStar_All.pipe_right uu___
            (FStar_TypeChecker_Env.norm_eff_name env) in
        let uu___ = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid in
        if uu___
        then u_res
        else
          (let is_total =
             let uu___2 = FStar_TypeChecker_Env.lookup_effect_quals env c_lid in
             FStar_All.pipe_right uu___2
               (FStar_List.existsb
                  (fun q -> q = FStar_Syntax_Syntax.TotalEffect)) in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu___3 = FStar_TypeChecker_Env.effect_repr env c u_res in
              match uu___3 with
              | FStar_Pervasives_Native.None ->
                  let uu___4 =
                    let uu___5 =
                      let uu___6 = FStar_Syntax_Print.lid_to_string c_lid in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu___6 in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu___5) in
                  FStar_Errors.raise_error uu___4 c.FStar_Syntax_Syntax.pos
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
      let uu___ = destruct_wp_comp ct in
      match uu___ with
      | (u_t, t, wp) ->
          let vc =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  FStar_All.pipe_right md
                    FStar_Syntax_Util.get_wp_trivial_combinator in
                FStar_All.pipe_right uu___3 FStar_Util.must in
              FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md uu___2 in
            let uu___2 =
              let uu___3 = FStar_Syntax_Syntax.as_arg t in
              let uu___4 =
                let uu___5 = FStar_Syntax_Syntax.as_arg wp in [uu___5] in
              uu___3 :: uu___4 in
            let uu___3 = FStar_TypeChecker_Env.get_range env in
            FStar_Syntax_Syntax.mk_Tm_app uu___1 uu___2 uu___3 in
          let uu___1 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc) in
          (ct, vc, uu___1)
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
                  let uu___ = FStar_TypeChecker_Env.try_lookup_lid env f in
                  match uu___ with
                  | FStar_Pervasives_Native.Some uu___1 ->
                      ((let uu___3 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions") in
                        if uu___3
                        then
                          let uu___4 = FStar_Ident.string_of_lid f in
                          FStar_Util.print1 "Coercing with %s!\n" uu___4
                        else ());
                       (let coercion =
                          let uu___3 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos in
                          FStar_Syntax_Syntax.fvar uu___3
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs in
                        let lc1 =
                          let uu___3 =
                            let uu___4 =
                              let uu___5 = mkcomp ty in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp uu___5 in
                            (FStar_Pervasives_Native.None, uu___4) in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu___3 in
                        let e1 =
                          let uu___3 =
                            let uu___4 = FStar_Syntax_Syntax.as_arg e in
                            [uu___4] in
                          FStar_Syntax_Syntax.mk_Tm_app coercion2 uu___3
                            e.FStar_Syntax_Syntax.pos in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None ->
                      ((let uu___2 =
                          let uu___3 =
                            let uu___4 = FStar_Ident.string_of_lid f in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu___4 in
                          (FStar_Errors.Warning_CoercionNotFound, uu___3) in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu___2);
                       (e, lc))
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee -> match projectee with | Yes _0 -> true | uu___ -> false
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee -> match projectee with | Yes _0 -> _0
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee -> match projectee with | Maybe -> true | uu___ -> false
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee -> match projectee with | No -> true | uu___ -> false
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
      let uu___ = FStar_Syntax_Util.head_and_args t2 in
      match uu___ with
      | (h, args) ->
          let h1 = FStar_Syntax_Util.un_uinst h in
          let r =
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Syntax_Subst.compress h1 in
                uu___3.FStar_Syntax_Syntax.n in
              (uu___2, args) in
            match uu___1 with
            | (FStar_Syntax_Syntax.Tm_fvar fv,
               (a, FStar_Pervasives_Native.None)::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu___2, uu___3) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown, uu___2) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match (uu___2, uu___3, branches),
               uu___4) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc ->
                        fun br ->
                          match acc with
                          | Yes uu___5 -> Maybe
                          | Maybe -> Maybe
                          | No ->
                              let uu___5 = FStar_Syntax_Subst.open_branch br in
                              (match uu___5 with
                               | (uu___6, uu___7, br_body) ->
                                   let uu___8 =
                                     let uu___9 =
                                       let uu___10 =
                                         let uu___11 =
                                           let uu___12 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names in
                                           FStar_All.pipe_right uu___12
                                             FStar_Util.set_elements in
                                         FStar_All.pipe_right uu___11
                                           (FStar_TypeChecker_Env.push_bvs
                                              env) in
                                       check_erased uu___10 in
                                     FStar_All.pipe_right br_body uu___9 in
                                   (match uu___8 with
                                    | No -> No
                                    | uu___9 -> Maybe))) No)
            | uu___2 -> No in
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
            (env.FStar_TypeChecker_Env.phase1 ||
               env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ()) in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
               let uu___1 =
                 let uu___2 = FStar_Syntax_Subst.compress t1 in
                 uu___2.FStar_Syntax_Syntax.n in
               match uu___1 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu___2 -> false in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
               let uu___1 =
                 let uu___2 = FStar_Syntax_Subst.compress t1 in
                 uu___2.FStar_Syntax_Syntax.n in
               match uu___1 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu___2 -> false in
             let is_type t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
               let t2 = FStar_Syntax_Util.unrefine t1 in
               let uu___1 =
                 let uu___2 = FStar_Syntax_Subst.compress t2 in
                 uu___2.FStar_Syntax_Syntax.n in
               match uu___1 with
               | FStar_Syntax_Syntax.Tm_type uu___2 -> true
               | uu___2 -> false in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ in
             let uu___1 = FStar_Syntax_Util.head_and_args res_typ in
             match uu___1 with
             | (head, args) ->
                 ((let uu___3 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions") in
                   if uu___3
                   then
                     let uu___4 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                     let uu___5 = FStar_Syntax_Print.term_to_string e in
                     let uu___6 = FStar_Syntax_Print.term_to_string res_typ in
                     let uu___7 = FStar_Syntax_Print.term_to_string exp_t in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu___4 uu___5 uu___6 uu___7
                   else ());
                  (let mk_erased u t =
                     let uu___3 =
                       let uu___4 =
                         fvar_const env FStar_Parser_Const.erased_lid in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu___4 [u] in
                     let uu___4 =
                       let uu___5 = FStar_Syntax_Syntax.as_arg t in [uu___5] in
                     FStar_Syntax_Util.mk_app uu___3 uu___4 in
                   let uu___3 =
                     let uu___4 =
                       let uu___5 = FStar_Syntax_Util.un_uinst head in
                       uu___5.FStar_Syntax_Syntax.n in
                     (uu___4, args) in
                   match uu___3 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type exp_t)
                       ->
                       let uu___4 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total in
                       (match uu___4 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu___4 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac in
                       (match uu___4 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu___4 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac in
                       (match uu___4 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu___4 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac in
                       (match uu___4 with
                        | (e1, lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu___4 ->
                       let uu___5 =
                         let uu___6 = check_erased env res_typ in
                         let uu___7 = check_erased env exp_t in
                         (uu___6, uu___7) in
                       (match uu___5 with
                        | (No, Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty in
                            let uu___6 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty in
                            (match uu___6 with
                             | FStar_Pervasives_Native.None ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e in
                                 let uu___7 =
                                   let uu___8 =
                                     let uu___9 = FStar_Syntax_Syntax.iarg ty in
                                     [uu___9] in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu___8
                                     FStar_Syntax_Syntax.mk_Total in
                                 (match uu___7 with
                                  | (e1, lc1) -> (e1, lc1, g1)))
                        | (Yes ty, No) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty in
                            let uu___6 =
                              let uu___7 =
                                let uu___8 = FStar_Syntax_Syntax.iarg ty in
                                [uu___8] in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu___7
                                FStar_Syntax_Syntax.mk_GTotal in
                            (match uu___6 with
                             | (e1, lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu___6 ->
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
        let uu___ = FStar_Syntax_Util.head_and_args rt1 in
        match uu___ with
        | (hd, args) ->
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Syntax_Subst.compress hd in
                uu___3.FStar_Syntax_Syntax.n in
              (uu___2, args) in
            (match uu___1 with
             | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu___2 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac in
                 FStar_All.pipe_left
                   (fun uu___3 -> FStar_Pervasives_Native.Some uu___3) uu___2
             | uu___2 -> FStar_Pervasives_Native.None)
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
          (let uu___1 = FStar_TypeChecker_Env.debug env FStar_Options.High in
           if uu___1
           then
             let uu___2 = FStar_Syntax_Print.term_to_string e in
             let uu___3 = FStar_TypeChecker_Common.lcomp_to_string lc in
             let uu___4 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu___2 uu___3 uu___4
           else ());
          (let use_eq =
             (env.FStar_TypeChecker_Env.use_eq_strict ||
                env.FStar_TypeChecker_Env.use_eq)
               ||
               (let uu___1 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name in
                match uu___1 with
                | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu___2 -> false) in
           let gopt =
             if use_eq
             then
               let uu___1 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t in
               (uu___1, false)
             else
               (let uu___2 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t in
                (uu___2, true)) in
           match gopt with
           | (FStar_Pervasives_Native.None, uu___1) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu___2 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ in
                 FStar_Errors.raise_error uu___2 e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___4 = lc in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___4.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___4.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___4.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g, apply_guard) ->
               let uu___1 = FStar_TypeChecker_Env.guard_form g in
               (match uu___1 with
                | FStar_TypeChecker_Common.Trivial ->
                    let strengthen_trivial uu___2 =
                      let uu___3 = FStar_TypeChecker_Common.lcomp_comp lc in
                      match uu___3 with
                      | (c, g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c in
                          let set_result_typ c1 =
                            FStar_Syntax_Util.set_result_typ c1 t in
                          let uu___4 =
                            let uu___5 = FStar_Syntax_Util.eq_tm t res_t in
                            uu___5 = FStar_Syntax_Util.Equal in
                          if uu___4
                          then
                            ((let uu___6 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu___6
                              then
                                let uu___7 =
                                  FStar_Syntax_Print.term_to_string res_t in
                                let uu___8 =
                                  FStar_Syntax_Print.term_to_string t in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu___7 uu___8
                              else ());
                             (let uu___6 = set_result_typ c in (uu___6, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu___6 -> true
                               | uu___6 -> false in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t in
                               let uu___6 =
                                 let uu___7 =
                                   let uu___8 =
                                     FStar_All.pipe_right c
                                       FStar_Syntax_Util.comp_effect_name in
                                   FStar_All.pipe_right uu___8
                                     (FStar_TypeChecker_Env.norm_eff_name env) in
                                 let uu___8 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env uu___7 (comp_univ_opt c)
                                   res_t uu___8 in
                               match uu___6 with
                               | (cret, gret) ->
                                   let lc1 =
                                     let uu___7 =
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                         c in
                                     let uu___8 =
                                       let uu___9 =
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                           cret in
                                       ((FStar_Pervasives_Native.Some x),
                                         uu___9) in
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (FStar_Pervasives_Native.Some e)
                                       uu___7 uu___8 in
                                   ((let uu___8 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme in
                                     if uu___8
                                     then
                                       let uu___9 =
                                         FStar_Syntax_Print.term_to_string e in
                                       let uu___10 =
                                         FStar_Syntax_Print.comp_to_string c in
                                       let uu___11 =
                                         FStar_Syntax_Print.term_to_string t in
                                       let uu___12 =
                                         FStar_TypeChecker_Common.lcomp_to_string
                                           lc1 in
                                       FStar_Util.print4
                                         "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                         uu___9 uu___10 uu___11 uu___12
                                     else ());
                                    (let uu___8 =
                                       FStar_TypeChecker_Common.lcomp_comp
                                         lc1 in
                                     match uu___8 with
                                     | (c1, g_lc) ->
                                         let uu___9 = set_result_typ c1 in
                                         let uu___10 =
                                           FStar_TypeChecker_Env.conj_guards
                                             [g_c; gret; g_lc] in
                                         (uu___9, uu___10)))
                             else
                               ((let uu___8 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu___8
                                 then
                                   let uu___9 =
                                     FStar_Syntax_Print.term_to_string res_t in
                                   let uu___10 =
                                     FStar_Syntax_Print.comp_to_string c in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu___9 uu___10
                                 else ());
                                (let uu___8 = set_result_typ c in
                                 (uu___8, g_c)))) in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___2 = g in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred_to_tac =
                          (uu___2.FStar_TypeChecker_Common.deferred_to_tac);
                        FStar_TypeChecker_Common.deferred =
                          (uu___2.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___2.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___2.FStar_TypeChecker_Common.implicits)
                      } in
                    let strengthen uu___2 =
                      let uu___3 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ()) in
                      if uu___3
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f in
                         let uu___5 =
                           let uu___6 = FStar_Syntax_Subst.compress f1 in
                           uu___6.FStar_Syntax_Syntax.n in
                         match uu___5 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu___6,
                              {
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Tm_fvar fv;
                                FStar_Syntax_Syntax.pos = uu___7;
                                FStar_Syntax_Syntax.vars = uu___8;_},
                              uu___9)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___10 = lc in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___10.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___10.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___10.FStar_TypeChecker_Common.comp_thunk)
                               } in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu___6 ->
                             let uu___7 =
                               FStar_TypeChecker_Common.lcomp_comp lc in
                             (match uu___7 with
                              | (c, g_c) ->
                                  ((let uu___9 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme in
                                    if uu___9
                                    then
                                      let uu___10 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ in
                                      let uu___11 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t in
                                      let uu___12 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c in
                                      let uu___13 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1 in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu___10 uu___11 uu___12 uu___13
                                    else ());
                                   (let u_t_opt = comp_univ_opt c in
                                    let x =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (t.FStar_Syntax_Syntax.pos)) t in
                                    let xexp =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu___9 =
                                      let uu___10 =
                                        let uu___11 =
                                          FStar_All.pipe_right c
                                            FStar_Syntax_Util.comp_effect_name in
                                        FStar_All.pipe_right uu___11
                                          (FStar_TypeChecker_Env.norm_eff_name
                                             env) in
                                      return_value env uu___10 u_t_opt t xexp in
                                    match uu___9 with
                                    | (cret, gret) ->
                                        let guard =
                                          if apply_guard
                                          then
                                            let uu___10 =
                                              let uu___11 =
                                                FStar_Syntax_Syntax.as_arg
                                                  xexp in
                                              [uu___11] in
                                            FStar_Syntax_Syntax.mk_Tm_app f1
                                              uu___10
                                              f1.FStar_Syntax_Syntax.pos
                                          else f1 in
                                        let uu___10 =
                                          let uu___11 =
                                            FStar_All.pipe_left
                                              (fun uu___12 ->
                                                 FStar_Pervasives_Native.Some
                                                   uu___12)
                                              (FStar_TypeChecker_Err.subtyping_failed
                                                 env
                                                 lc.FStar_TypeChecker_Common.res_typ
                                                 t) in
                                          let uu___12 =
                                            let uu___13 =
                                              FStar_TypeChecker_Env.push_bvs
                                                env [x] in
                                            FStar_TypeChecker_Env.set_range
                                              uu___13
                                              e.FStar_Syntax_Syntax.pos in
                                          let uu___13 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              cret in
                                          let uu___14 =
                                            FStar_All.pipe_left
                                              FStar_TypeChecker_Env.guard_of_guard_formula
                                              (FStar_TypeChecker_Common.NonTrivial
                                                 guard) in
                                          strengthen_precondition uu___11
                                            uu___12 e uu___13 uu___14 in
                                        (match uu___10 with
                                         | (eq_ret,
                                            _trivial_so_ok_to_discard) ->
                                             let x1 =
                                               let uu___11 = x in
                                               {
                                                 FStar_Syntax_Syntax.ppname =
                                                   (uu___11.FStar_Syntax_Syntax.ppname);
                                                 FStar_Syntax_Syntax.index =
                                                   (uu___11.FStar_Syntax_Syntax.index);
                                                 FStar_Syntax_Syntax.sort =
                                                   (lc.FStar_TypeChecker_Common.res_typ)
                                               } in
                                             let c1 =
                                               let uu___11 =
                                                 FStar_TypeChecker_Common.lcomp_of_comp
                                                   c in
                                               bind e.FStar_Syntax_Syntax.pos
                                                 env
                                                 (FStar_Pervasives_Native.Some
                                                    e) uu___11
                                                 ((FStar_Pervasives_Native.Some
                                                     x1), eq_ret) in
                                             let uu___11 =
                                               FStar_TypeChecker_Common.lcomp_comp
                                                 c1 in
                                             (match uu___11 with
                                              | (c2, g_lc) ->
                                                  ((let uu___13 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        FStar_Options.Extreme in
                                                    if uu___13
                                                    then
                                                      let uu___14 =
                                                        FStar_TypeChecker_Normalize.comp_to_string
                                                          env c2 in
                                                      FStar_Util.print1
                                                        "Strengthened to %s\n"
                                                        uu___14
                                                    else ());
                                                   (let uu___13 =
                                                      FStar_TypeChecker_Env.conj_guards
                                                        [g_c; gret; g_lc] in
                                                    (c2, uu___13))))))))) in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___2 ->
                              match uu___2 with
                              | FStar_Syntax_Syntax.RETURN ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu___3 -> [])) in
                    let lc1 =
                      let uu___2 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name in
                      FStar_TypeChecker_Common.mk_lcomp uu___2 t flags
                        strengthen in
                    let g2 =
                      let uu___2 = g1 in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred_to_tac =
                          (uu___2.FStar_TypeChecker_Common.deferred_to_tac);
                        FStar_TypeChecker_Common.deferred =
                          (uu___2.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___2.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___2.FStar_TypeChecker_Common.implicits)
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
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_Syntax_Syntax.as_arg uu___3 in
            [uu___2] in
          FStar_Syntax_Syntax.mk_Tm_app ens uu___1
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu___ in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t in
      let uu___ = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu___
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu___2 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu___2 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu___2 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid) in
             if uu___2
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req, uu___3)::(ens, uu___4)::uu___5 ->
                    let uu___6 =
                      let uu___7 = norm req in
                      FStar_Pervasives_Native.Some uu___7 in
                    let uu___7 =
                      let uu___8 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu___8 in
                    (uu___6, uu___7)
                | uu___3 ->
                    let uu___4 =
                      let uu___5 =
                        let uu___6 = FStar_Syntax_Print.comp_to_string comp in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu___6 in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu___5) in
                    FStar_Errors.raise_error uu___4
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp, uu___4)::uu___5 ->
                    let uu___6 =
                      let uu___7 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst uu___7 in
                    (match uu___6 with
                     | (us_r, uu___7) ->
                         let uu___8 =
                           let uu___9 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu___9 in
                         (match uu___8 with
                          | (us_e, uu___9) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu___10 =
                                  let uu___11 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r in
                                  FStar_Syntax_Syntax.fvar uu___11
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu___10 us_r in
                              let as_ens =
                                let uu___10 =
                                  let uu___11 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r in
                                  FStar_Syntax_Syntax.fvar uu___11
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu___10 us_e in
                              let req =
                                let uu___10 =
                                  let uu___11 =
                                    let uu___12 =
                                      FStar_Syntax_Syntax.as_arg wp in
                                    [uu___12] in
                                  ((ct1.FStar_Syntax_Syntax.result_typ),
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.imp_tag))
                                    :: uu___11 in
                                FStar_Syntax_Syntax.mk_Tm_app as_req uu___10
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu___10 =
                                  let uu___11 =
                                    let uu___12 =
                                      FStar_Syntax_Syntax.as_arg wp in
                                    [uu___12] in
                                  ((ct1.FStar_Syntax_Syntax.result_typ),
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.imp_tag))
                                    :: uu___11 in
                                FStar_Syntax_Syntax.mk_Tm_app as_ens uu___10
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu___10 =
                                let uu___11 = norm req in
                                FStar_Pervasives_Native.Some uu___11 in
                              let uu___11 =
                                let uu___12 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu___12 in
                              (uu___10, uu___11)))
                | uu___4 -> failwith "Impossible"))
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
        (let uu___1 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu___1
         then
           let uu___2 = FStar_Syntax_Print.term_to_string tm in
           let uu___3 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu___2 uu___3
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
          (let uu___1 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify") in
           if uu___1
           then
             let uu___2 = FStar_Syntax_Print.term_to_string tm in
             let uu___3 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu___2 uu___3
           else ());
          tm'
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu___ =
      let uu___1 =
        let uu___2 = FStar_Syntax_Subst.compress t in
        uu___2.FStar_Syntax_Syntax.n in
      match uu___1 with
      | FStar_Syntax_Syntax.Tm_app uu___2 -> false
      | uu___2 -> true in
    if uu___
    then t
    else
      (let uu___2 = FStar_Syntax_Util.head_and_args t in
       match uu___2 with
       | (head, args) ->
           let uu___3 =
             let uu___4 =
               let uu___5 = FStar_Syntax_Subst.compress head in
               uu___5.FStar_Syntax_Syntax.n in
             match uu___4 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) ->
                 true
             | uu___5 -> false in
           if uu___3
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu___4 ->
                  failwith
                    "Impossible : Reify applied to multiple arguments after normalization.")
           else t)
let (maybe_implicit_with_meta_or_attr :
  FStar_Syntax_Syntax.aqual ->
    FStar_Syntax_Syntax.attribute Prims.list -> Prims.bool)
  =
  fun aq ->
    fun attrs ->
      match (aq, attrs) with
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta uu___),
         uu___1) -> true
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit uu___),
         uu___1::uu___2) -> true
      | uu___ -> false
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
          ((let uu___2 = FStar_TypeChecker_Env.debug env FStar_Options.High in
            if uu___2
            then
              let uu___3 = FStar_Syntax_Print.term_to_string e in
              let uu___4 = FStar_Syntax_Print.term_to_string t in
              let uu___5 =
                let uu___6 = FStar_TypeChecker_Env.expected_typ env in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu___6 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu___3 uu___4 uu___5
            else ());
           (let unfolded_arrow_formals t1 =
              let rec aux bs t2 =
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf env t2 in
                let uu___2 = FStar_Syntax_Util.arrow_formals t3 in
                match uu___2 with
                | (bs', t4) ->
                    (match bs' with
                     | [] -> bs
                     | bs'1 -> aux (FStar_List.append bs bs'1) t4) in
              aux [] t1 in
            let number_of_implicits t1 =
              let formals = unfolded_arrow_formals t1 in
              let n_implicits =
                let uu___2 =
                  FStar_All.pipe_right formals
                    (FStar_Util.prefix_until
                       (fun uu___3 ->
                          match uu___3 with
                          | { FStar_Syntax_Syntax.binder_bv = uu___4;
                              FStar_Syntax_Syntax.binder_qual = imp;
                              FStar_Syntax_Syntax.binder_attrs = uu___5;_} ->
                              (FStar_Option.isNone imp) ||
                                (let uu___6 =
                                   FStar_Syntax_Util.eq_aqual imp
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Equality) in
                                 uu___6 = FStar_Syntax_Util.Equal))) in
                match uu___2 with
                | FStar_Pervasives_Native.None -> FStar_List.length formals
                | FStar_Pervasives_Native.Some
                    (implicits, _first_explicit, _rest) ->
                    FStar_List.length implicits in
              n_implicits in
            let inst_n_binders t1 =
              let uu___2 = FStar_TypeChecker_Env.expected_typ env in
              match uu___2 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t in
                  let n_available = number_of_implicits t1 in
                  if n_available < n_expected
                  then
                    let uu___3 =
                      let uu___4 =
                        let uu___5 = FStar_Util.string_of_int n_expected in
                        let uu___6 = FStar_Syntax_Print.term_to_string e in
                        let uu___7 = FStar_Util.string_of_int n_available in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu___5 uu___6 uu___7 in
                      (FStar_Errors.Fatal_MissingImplicitArguments, uu___4) in
                    let uu___4 = FStar_TypeChecker_Env.get_range env in
                    FStar_Errors.raise_error uu___3 uu___4
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected) in
            let decr_inst uu___2 =
              match uu___2 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one) in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                let uu___2 = FStar_Syntax_Subst.open_comp bs c in
                (match uu___2 with
                 | (bs1, c1) ->
                     let rec aux subst inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some uu___3, uu___4) when
                           uu___3 = Prims.int_zero ->
                           ([], bs2, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu___3,
                          { FStar_Syntax_Syntax.binder_bv = x;
                            FStar_Syntax_Syntax.binder_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu___4);
                            FStar_Syntax_Syntax.binder_attrs = [];_}::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort in
                           let uu___5 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2 in
                           (match uu___5 with
                            | (v, uu___6, g) ->
                                ((let uu___8 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High in
                                  if uu___8
                                  then
                                    let uu___9 =
                                      FStar_Syntax_Print.term_to_string v in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu___9
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst in
                                  let uu___8 =
                                    aux subst1 (decr_inst inst_n) rest in
                                  match uu___8 with
                                  | (args, bs3, subst2, g') ->
                                      let uu___9 =
                                        FStar_TypeChecker_Env.conj_guard g g' in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu___9))))
                       | (uu___3,
                          { FStar_Syntax_Syntax.binder_bv = x;
                            FStar_Syntax_Syntax.binder_qual = qual;
                            FStar_Syntax_Syntax.binder_attrs = attrs;_}::rest)
                           when maybe_implicit_with_meta_or_attr qual attrs
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort in
                           let meta_t =
                             match (qual, attrs) with
                             | (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Syntax.Meta tau), uu___4) ->
                                 let uu___5 =
                                   let uu___6 = FStar_Dyn.mkdyn env in
                                   (uu___6, tau) in
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_tac uu___5
                             | (uu___4, attr::uu___5) ->
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_attr attr
                             | uu___4 ->
                                 failwith
                                   "Impossible, match is under a guard, did not expect this case" in
                           let uu___4 =
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict
                               (FStar_Pervasives_Native.Some meta_t) in
                           (match uu___4 with
                            | (v, uu___5, g) ->
                                ((let uu___7 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High in
                                  if uu___7
                                  then
                                    let uu___8 =
                                      FStar_Syntax_Print.term_to_string v in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu___8
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst in
                                  let uu___7 =
                                    aux subst1 (decr_inst inst_n) rest in
                                  match uu___7 with
                                  | (args, bs3, subst2, g') ->
                                      let uu___8 =
                                        FStar_TypeChecker_Env.conj_guard g g' in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu___8))))
                       | (uu___3, bs3) ->
                           ([], bs3, subst,
                             FStar_TypeChecker_Env.trivial_guard) in
                     let uu___3 =
                       let uu___4 = inst_n_binders t1 in aux [] uu___4 bs1 in
                     (match uu___3 with
                      | (args, bs2, subst, guard) ->
                          (match (args, bs2) with
                           | ([], uu___4) -> (e, torig, guard)
                           | (uu___4, []) when
                               let uu___5 =
                                 FStar_Syntax_Util.is_total_comp c1 in
                               Prims.op_Negation uu___5 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu___4 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu___5 -> FStar_Syntax_Util.arrow bs2 c1 in
                               let t3 = FStar_Syntax_Subst.subst subst t2 in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   e.FStar_Syntax_Syntax.pos in
                               (e1, t3, guard))))
            | uu___2 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
let (check_has_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun e ->
      fun t1 ->
        fun t2 ->
          let env1 =
            FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
          let g_opt =
            if env1.FStar_TypeChecker_Env.use_eq_strict
            then
              let uu___ = FStar_TypeChecker_Rel.teq_nosmt_force env1 t1 t2 in
              (if uu___
               then
                 FStar_All.pipe_right FStar_TypeChecker_Env.trivial_guard
                   (fun uu___1 -> FStar_Pervasives_Native.Some uu___1)
               else FStar_Pervasives_Native.None)
            else
              if env1.FStar_TypeChecker_Env.use_eq
              then FStar_TypeChecker_Rel.try_teq true env1 t1 t2
              else
                (let uu___2 =
                   FStar_TypeChecker_Rel.get_subtyping_predicate env1 t1 t2 in
                 match uu___2 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some f ->
                     let uu___3 = FStar_TypeChecker_Env.apply_guard f e in
                     FStar_All.pipe_right uu___3
                       (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)) in
          match g_opt with
          | FStar_Pervasives_Native.None ->
              let uu___ =
                FStar_TypeChecker_Err.expected_expression_of_type env1 t2 e
                  t1 in
              let uu___1 = FStar_TypeChecker_Env.get_range env1 in
              FStar_Errors.raise_error uu___ uu___1
          | FStar_Pervasives_Native.Some g -> g
let (check_has_type_maybe_coerce :
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
          let uu___ = maybe_coerce_lc env1 e lc t2 in
          match uu___ with
          | (e1, lc1, g_c) ->
              let g =
                check_has_type env1 e1 lc1.FStar_TypeChecker_Common.res_typ
                  t2 in
              ((let uu___2 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel") in
                if uu___2
                then
                  let uu___3 = FStar_TypeChecker_Rel.guard_to_string env1 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu___3
                else ());
               (let uu___2 = FStar_TypeChecker_Env.conj_guard g g_c in
                (e1, lc1, uu___2)))
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env ->
    fun g ->
      fun lc ->
        (let uu___1 = FStar_TypeChecker_Env.debug env FStar_Options.Medium in
         if uu___1
         then
           let uu___2 = FStar_TypeChecker_Common.lcomp_to_string lc in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu___2
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
         let uu___1 = FStar_TypeChecker_Common.lcomp_comp lc in
         match uu___1 with
         | (c, g_c) ->
             let uu___2 = FStar_TypeChecker_Common.is_total_lcomp lc in
             if uu___2
             then
               let uu___3 =
                 let uu___4 = FStar_TypeChecker_Env.conj_guard g1 g_c in
                 discharge uu___4 in
               (uu___3, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] in
                let c1 =
                  let uu___4 =
                    let uu___5 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    FStar_All.pipe_right uu___5 FStar_Syntax_Syntax.mk_Comp in
                  FStar_All.pipe_right uu___4
                    (FStar_TypeChecker_Normalize.normalize_comp steps env) in
                let uu___4 = check_trivial_precondition env c1 in
                match uu___4 with
                | (ct, vc, g_pre) ->
                    ((let uu___6 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification") in
                      if uu___6
                      then
                        let uu___7 = FStar_Syntax_Print.term_to_string vc in
                        FStar_Util.print1 "top-level VC: %s\n" uu___7
                      else ());
                     (let uu___6 =
                        let uu___7 =
                          let uu___8 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre in
                          FStar_TypeChecker_Env.conj_guard g1 uu___8 in
                        discharge uu___7 in
                      let uu___7 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp in
                      (uu___6, uu___7)))))
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head ->
    fun seen_args ->
      let short_bin_op f uu___ =
        match uu___ with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst, uu___1)::[] -> f fst
        | uu___1 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu___ = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu___
          (fun uu___1 -> FStar_TypeChecker_Common.NonTrivial uu___1) in
      let op_or_e e =
        let uu___ =
          let uu___1 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu___1 in
        FStar_All.pipe_right uu___
          (fun uu___1 -> FStar_TypeChecker_Common.NonTrivial uu___1) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun uu___ -> FStar_TypeChecker_Common.NonTrivial uu___) in
      let op_or_t t =
        let uu___ = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu___
          (fun uu___1 -> FStar_TypeChecker_Common.NonTrivial uu___1) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun uu___ -> FStar_TypeChecker_Common.NonTrivial uu___) in
      let short_op_ite uu___ =
        match uu___ with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard, uu___1)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard, uu___1)::[] ->
            let uu___2 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu___2
              (fun uu___3 -> FStar_TypeChecker_Common.NonTrivial uu___3)
        | uu___1 -> failwith "Unexpected args to ITE" in
      let table =
        let uu___ =
          let uu___1 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu___1) in
        let uu___1 =
          let uu___2 =
            let uu___3 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu___3) in
          let uu___3 =
            let uu___4 =
              let uu___5 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu___5) in
            let uu___5 =
              let uu___6 =
                let uu___7 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu___7) in
              let uu___7 =
                let uu___8 =
                  let uu___9 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu___9) in
                [uu___8; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu___6 :: uu___7 in
            uu___4 :: uu___5 in
          uu___2 :: uu___3 in
        uu___ :: uu___1 in
      match head.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu___ =
            FStar_Util.find_map table
              (fun uu___1 ->
                 match uu___1 with
                 | (x, mk) ->
                     let uu___2 = FStar_Ident.lid_equals x lid in
                     if uu___2
                     then
                       let uu___3 = mk seen_args in
                       FStar_Pervasives_Native.Some uu___3
                     else FStar_Pervasives_Native.None) in
          (match uu___ with
           | FStar_Pervasives_Native.None -> FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu___ -> FStar_TypeChecker_Common.Trivial
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l ->
    let uu___ =
      let uu___1 = FStar_Syntax_Util.un_uinst l in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu___1 -> false
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env ->
    fun bs ->
      let pos bs1 =
        match bs1 with
        | { FStar_Syntax_Syntax.binder_bv = hd;
            FStar_Syntax_Syntax.binder_qual = uu___;
            FStar_Syntax_Syntax.binder_attrs = uu___1;_}::uu___2 ->
            FStar_Syntax_Syntax.range_of_bv hd
        | uu___ -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | { FStar_Syntax_Syntax.binder_bv = uu___;
          FStar_Syntax_Syntax.binder_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Implicit uu___1);
          FStar_Syntax_Syntax.binder_attrs = uu___2;_}::uu___3 -> bs
      | uu___ ->
          let uu___1 = FStar_TypeChecker_Env.expected_typ env in
          (match uu___1 with
           | FStar_Pervasives_Native.None -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu___2 =
                 let uu___3 = FStar_Syntax_Subst.compress t in
                 uu___3.FStar_Syntax_Syntax.n in
               (match uu___2 with
                | FStar_Syntax_Syntax.Tm_arrow (bs', uu___3) ->
                    let uu___4 =
                      FStar_Util.prefix_until
                        (fun uu___5 ->
                           match uu___5 with
                           | { FStar_Syntax_Syntax.binder_bv = uu___6;
                               FStar_Syntax_Syntax.binder_qual =
                                 FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu___7);
                               FStar_Syntax_Syntax.binder_attrs = uu___8;_}
                               -> false
                           | uu___6 -> true) bs' in
                    (match uu___4 with
                     | FStar_Pervasives_Native.None -> bs
                     | FStar_Pervasives_Native.Some ([], uu___5, uu___6) ->
                         bs
                     | FStar_Pervasives_Native.Some (imps, uu___5, uu___6) ->
                         let uu___7 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu___8 ->
                                   match uu___8 with
                                   | { FStar_Syntax_Syntax.binder_bv = x;
                                       FStar_Syntax_Syntax.binder_qual =
                                         uu___9;
                                       FStar_Syntax_Syntax.binder_attrs =
                                         uu___10;_}
                                       ->
                                       let uu___11 =
                                         FStar_Ident.string_of_id
                                           x.FStar_Syntax_Syntax.ppname in
                                       FStar_Util.starts_with uu___11 "'")) in
                         if uu___7
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun b ->
                                     let uu___8 = b in
                                     let uu___9 =
                                       FStar_Syntax_Syntax.set_range_of_bv
                                         b.FStar_Syntax_Syntax.binder_bv r in
                                     {
                                       FStar_Syntax_Syntax.binder_bv = uu___9;
                                       FStar_Syntax_Syntax.binder_qual =
                                         (uu___8.FStar_Syntax_Syntax.binder_qual);
                                       FStar_Syntax_Syntax.binder_attrs =
                                         (uu___8.FStar_Syntax_Syntax.binder_attrs)
                                     })) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu___3 -> bs))
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
            let uu___ =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1)) in
            if uu___
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
          let uu___ =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu___
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
        (let uu___1 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu___1
         then
           ((let uu___3 = FStar_Ident.string_of_lid lident in d uu___3);
            (let uu___3 = FStar_Ident.string_of_lid lident in
             let uu___4 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu___3 uu___4))
         else ());
        (let fv =
           let uu___1 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu___1
             FStar_Pervasives_Native.None in
         let lbname = FStar_Pervasives.Inr fv in
         let lb =
           (false,
             [FStar_Syntax_Util.mk_letbinding lbname []
                FStar_Syntax_Syntax.tun FStar_Parser_Const.effect_Tot_lid def
                [] FStar_Range.dummyRange]) in
         let sig_ctx =
           FStar_Syntax_Syntax.mk_sigelt
             (FStar_Syntax_Syntax.Sig_let (lb, [lident])) in
         let uu___1 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Range.dummyRange in
         ((let uu___2 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel = (uu___2.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng = (uu___2.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2.FStar_Syntax_Syntax.sigopts)
           }), uu___1))
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env ->
    fun se ->
      let visibility uu___ =
        match uu___ with
        | FStar_Syntax_Syntax.Private -> true
        | uu___1 -> false in
      let reducibility uu___ =
        match uu___ with
        | FStar_Syntax_Syntax.Irreducible -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> true
        | FStar_Syntax_Syntax.Visible_default -> true
        | FStar_Syntax_Syntax.Inline_for_extraction -> true
        | uu___1 -> false in
      let assumption uu___ =
        match uu___ with
        | FStar_Syntax_Syntax.Assumption -> true
        | FStar_Syntax_Syntax.New -> true
        | uu___1 -> false in
      let reification uu___ =
        match uu___ with
        | FStar_Syntax_Syntax.Reifiable -> true
        | FStar_Syntax_Syntax.Reflectable uu___1 -> true
        | uu___1 -> false in
      let inferred uu___ =
        match uu___ with
        | FStar_Syntax_Syntax.Discriminator uu___1 -> true
        | FStar_Syntax_Syntax.Projector uu___1 -> true
        | FStar_Syntax_Syntax.RecordType uu___1 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu___1 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor -> true
        | FStar_Syntax_Syntax.HasMaskedEffect -> true
        | FStar_Syntax_Syntax.Effect -> true
        | uu___1 -> false in
      let has_eq uu___ =
        match uu___ with
        | FStar_Syntax_Syntax.Noeq -> true
        | FStar_Syntax_Syntax.Unopteq -> true
        | uu___1 -> false in
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
                    (((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                           (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Visible_default ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    (((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                           (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Irreducible ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    (((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                           (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Noeq ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    (((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                           (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Unopteq ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    (((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                           (x = FStar_Syntax_Syntax.Inline_for_extraction))
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
        | FStar_Syntax_Syntax.Reflectable uu___ ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private -> true
        | uu___ -> true in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1 in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l ->
                  let uu___ = FStar_TypeChecker_Env.try_lookup_val_decl env l in
                  FStar_Option.isSome uu___)) in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu___ = FStar_Option.get attrs_opt in
                     FStar_Syntax_Util.has_attribute uu___
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
           | FStar_Syntax_Syntax.Sig_bundle uu___2 ->
               let uu___3 =
                 let uu___4 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___5 ->
                           match uu___5 with
                           | FStar_Syntax_Syntax.Noeq -> true
                           | uu___6 -> false)) in
                 Prims.op_Negation uu___4 in
               if uu___3
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu___2 -> ()
           | FStar_Syntax_Syntax.Sig_fail uu___2 -> ()
           | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu___2) ->
               let uu___3 =
                 FStar_Syntax_Util.abs_formals lb.FStar_Syntax_Syntax.lbdef in
               (match uu___3 with
                | (uu___4, body, uu___5) ->
                    let uu___6 =
                      let uu___7 =
                        FStar_TypeChecker_Normalize.non_info_norm env body in
                      Prims.op_Negation uu___7 in
                    if uu___6
                    then
                      let uu___7 =
                        let uu___8 =
                          let uu___9 = FStar_Syntax_Print.term_to_string body in
                          FStar_Util.format1
                            "Illegal attribute: the `erasable` attribute is only permitted on inductive type definitions and abbreviations for non-informative types. %s is considered informative."
                            uu___9 in
                        (FStar_Errors.Fatal_QulifierListNotPermitted, uu___8) in
                      FStar_Errors.raise_error uu___7
                        body.FStar_Syntax_Syntax.pos
                    else ())
           | FStar_Syntax_Syntax.Sig_new_effect
               { FStar_Syntax_Syntax.mname = eff_name;
                 FStar_Syntax_Syntax.cattributes = uu___2;
                 FStar_Syntax_Syntax.univs = uu___3;
                 FStar_Syntax_Syntax.binders = uu___4;
                 FStar_Syntax_Syntax.signature = uu___5;
                 FStar_Syntax_Syntax.combinators = uu___6;
                 FStar_Syntax_Syntax.actions = uu___7;
                 FStar_Syntax_Syntax.eff_attrs = uu___8;_}
               ->
               if
                 Prims.op_Negation
                   (FStar_List.contains FStar_Syntax_Syntax.TotalEffect quals)
               then
                 let uu___9 =
                   let uu___10 =
                     let uu___11 = FStar_Ident.string_of_lid eff_name in
                     FStar_Util.format1
                       "Effect %s is marked erasable but only total effects are allowed to be erasable"
                       uu___11 in
                   (FStar_Errors.Fatal_QulifierListNotPermitted, uu___10) in
                 FStar_Errors.raise_error uu___9 r
               else ()
           | uu___2 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_QulifierListNotPermitted,
                   "Illegal attribute: the `erasable` attribute is only permitted on inductive type definitions and abbreviations for non-informative types")
                 r)
        else () in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic))) in
      let uu___ =
        let uu___1 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___2 ->
                  match uu___2 with
                  | FStar_Syntax_Syntax.OnlyName -> true
                  | uu___3 -> false)) in
        FStar_All.pipe_right uu___1 Prims.op_Negation in
      if uu___
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x -> fun y -> x = y) quals in
        let err' msg =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Print.quals_to_string quals in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu___3 msg in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu___2) in
          FStar_Errors.raise_error uu___1 r in
        let err msg = err' (Prims.op_Hat ": " msg) in
        let err'1 uu___1 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu___3 =
            let uu___4 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu___4 in
          if uu___3 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec, uu___4), uu___5) ->
              ((let uu___7 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu___7
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu___7 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x -> (assumption x) || (has_eq x))) in
                if uu___7
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu___4 ->
              ((let uu___6 =
                  let uu___7 =
                    FStar_All.pipe_right quals
                      (FStar_Util.for_all
                         (fun x ->
                            ((((x = FStar_Syntax_Syntax.Inline_for_extraction)
                                 || (x = FStar_Syntax_Syntax.NoExtract))
                                || (inferred x))
                               || (visibility x))
                              || (has_eq x))) in
                  Prims.op_Negation uu___7 in
                if uu___6 then err'1 () else ());
               (let uu___6 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___7 ->
                           match uu___7 with
                           | FStar_Syntax_Syntax.Unopteq -> true
                           | uu___8 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr) in
                if uu___6
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu___4 ->
              let uu___5 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu___5 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu___4 ->
              let uu___5 =
                let uu___6 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu___6 in
              if uu___5 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu___4 ->
              let uu___5 =
                let uu___6 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu___6 in
              if uu___5 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu___4 ->
              let uu___5 =
                let uu___6 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu___6 in
              if uu___5 then err'1 () else ()
          | uu___4 -> ()))
      else ()
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g ->
    fun t ->
      let rec descend env t1 =
        let uu___ =
          let uu___1 = FStar_Syntax_Subst.compress t1 in
          uu___1.FStar_Syntax_Syntax.n in
        match uu___ with
        | FStar_Syntax_Syntax.Tm_arrow uu___1 ->
            let uu___2 = FStar_Syntax_Util.arrow_formals_comp t1 in
            (match uu___2 with
             | (bs, c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs in
                 (FStar_TypeChecker_Env.is_erasable_effect env1
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu___1;
               FStar_Syntax_Syntax.index = uu___2;
               FStar_Syntax_Syntax.sort = t2;_},
             uu___3)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head, uu___1) -> descend env head
        | FStar_Syntax_Syntax.Tm_uinst (head, uu___1) -> descend env head
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu___1 -> false
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
        (let uu___1 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction") in
         if uu___1
         then
           let uu___2 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu___2
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
                  let uu___ =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t in
                  FStar_Errors.raise_error uu___ r in
                let uu___ = FStar_TypeChecker_Env.inst_tscheme signature_ts in
                match uu___ with
                | (uu___1, signature) ->
                    let uu___2 =
                      let uu___3 = FStar_Syntax_Subst.compress signature in
                      uu___3.FStar_Syntax_Syntax.n in
                    (match uu___2 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs, uu___3) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs in
                         (match bs1 with
                          | a::bs2 ->
                              let uu___4 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((a.FStar_Syntax_Syntax.binder_bv),
                                       a_tm)]
                                  (fun b ->
                                     let uu___5 =
                                       FStar_Syntax_Print.binder_to_string b in
                                     let uu___6 =
                                       FStar_Ident.string_of_lid eff_name in
                                     let uu___7 =
                                       FStar_Range.string_of_range r in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu___5 uu___6 uu___7) r in
                              (match uu___4 with
                               | (is, g) ->
                                   let uu___5 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None ->
                                         let eff_c =
                                           let uu___6 =
                                             let uu___7 =
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
                                                 = uu___7;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp uu___6 in
                                         let uu___6 =
                                           let uu___7 =
                                             let uu___8 =
                                               let uu___9 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   FStar_Syntax_Syntax.t_unit in
                                               [uu___9] in
                                             (uu___8, eff_c) in
                                           FStar_Syntax_Syntax.Tm_arrow
                                             uu___7 in
                                         FStar_Syntax_Syntax.mk uu___6 r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu___6 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u] in
                                           FStar_All.pipe_right uu___6
                                             FStar_Pervasives_Native.snd in
                                         let is_args =
                                           FStar_List.map2
                                             (fun i ->
                                                fun uu___6 ->
                                                  match uu___6 with
                                                  | {
                                                      FStar_Syntax_Syntax.binder_bv
                                                        = uu___7;
                                                      FStar_Syntax_Syntax.binder_qual
                                                        = aqual;
                                                      FStar_Syntax_Syntax.binder_attrs
                                                        = uu___8;_}
                                                      -> (i, aqual)) is bs2 in
                                         let uu___6 =
                                           let uu___7 =
                                             FStar_Syntax_Syntax.as_arg a_tm in
                                           uu___7 :: is_args in
                                         FStar_Syntax_Syntax.mk_Tm_app repr
                                           uu___6 r in
                                   (uu___5, g))
                          | uu___4 -> fail signature)
                     | uu___3 -> fail signature)
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
            let uu___ =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env) in
            FStar_All.pipe_right uu___
              (fun ed ->
                 let uu___1 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu___1 u a_tm)
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
              let uu___ = FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u] in
              match uu___ with
              | (uu___1, sig_tm) ->
                  let fail t =
                    let uu___2 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t in
                    FStar_Errors.raise_error uu___2 r in
                  let uu___2 =
                    let uu___3 = FStar_Syntax_Subst.compress sig_tm in
                    uu___3.FStar_Syntax_Syntax.n in
                  (match uu___2 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs, uu___3) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs in
                       (match bs1 with
                        | { FStar_Syntax_Syntax.binder_bv = a';
                            FStar_Syntax_Syntax.binder_qual = uu___4;
                            FStar_Syntax_Syntax.binder_attrs = uu___5;_}::bs2
                            ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu___4 -> fail sig_tm)
                   | uu___3 -> fail sig_tm)
let (check_non_informative_type_for_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.term -> FStar_Range.range -> unit)
  =
  fun env ->
    fun m1 ->
      fun m2 ->
        fun t ->
          fun r ->
            let uu___ =
              ((FStar_TypeChecker_Env.is_erasable_effect env m1) &&
                 (let uu___1 =
                    FStar_TypeChecker_Env.is_erasable_effect env m2 in
                  Prims.op_Negation uu___1))
                &&
                (let uu___1 = FStar_TypeChecker_Normalize.non_info_norm env t in
                 Prims.op_Negation uu___1) in
            if uu___
            then
              let uu___1 =
                let uu___2 =
                  let uu___3 = FStar_Ident.string_of_lid m1 in
                  let uu___4 = FStar_Ident.string_of_lid m2 in
                  let uu___5 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.format3
                    "Cannot lift erasable expression from %s ~> %s since its type %s is informative"
                    uu___3 uu___4 uu___5 in
                (FStar_Errors.Error_TypeError, uu___2) in
              FStar_Errors.raise_error uu___1 r
            else ()
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
          (let uu___1 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects") in
           if uu___1
           then
             let uu___2 = FStar_Syntax_Print.comp_to_string c in
             let uu___3 = FStar_Syntax_Print.lid_to_string tgt in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu___2 uu___3
           else ());
          (let r = FStar_TypeChecker_Env.get_range env in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c in
           check_non_informative_type_for_lift env
             ct.FStar_Syntax_Syntax.effect_name tgt
             ct.FStar_Syntax_Syntax.result_typ r;
           (let lift_name =
              let uu___2 =
                FStar_Ident.string_of_lid ct.FStar_Syntax_Syntax.effect_name in
              let uu___3 = FStar_Ident.string_of_lid tgt in
              FStar_Util.format2 "%s ~> %s" uu___2 uu___3 in
            let uu___2 =
              let uu___3 = FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs in
              let uu___4 =
                FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                  (FStar_List.map FStar_Pervasives_Native.fst) in
              (uu___3, (ct.FStar_Syntax_Syntax.result_typ), uu___4) in
            match uu___2 with
            | (u, a, c_is) ->
                let uu___3 =
                  FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u] in
                (match uu___3 with
                 | (uu___4, lift_t) ->
                     let lift_t_shape_error s =
                       let uu___5 =
                         FStar_Ident.string_of_lid
                           ct.FStar_Syntax_Syntax.effect_name in
                       let uu___6 = FStar_Ident.string_of_lid tgt in
                       let uu___7 = FStar_Syntax_Print.term_to_string lift_t in
                       FStar_Util.format4
                         "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                         uu___5 uu___6 s uu___7 in
                     let uu___5 =
                       let uu___6 =
                         let uu___7 = FStar_Syntax_Subst.compress lift_t in
                         uu___7.FStar_Syntax_Syntax.n in
                       match uu___6 with
                       | FStar_Syntax_Syntax.Tm_arrow (bs, c1) when
                           (FStar_List.length bs) >= (Prims.of_int (2)) ->
                           let uu___7 = FStar_Syntax_Subst.open_comp bs c1 in
                           (match uu___7 with
                            | (a_b::bs1, c2) ->
                                let uu___8 =
                                  FStar_All.pipe_right bs1
                                    (FStar_List.splitAt
                                       ((FStar_List.length bs1) -
                                          Prims.int_one)) in
                                (a_b, uu___8, c2))
                       | uu___7 ->
                           let uu___8 =
                             let uu___9 =
                               lift_t_shape_error
                                 "either not an arrow or not enough binders" in
                             (FStar_Errors.Fatal_UnexpectedEffect, uu___9) in
                           FStar_Errors.raise_error uu___8 r in
                     (match uu___5 with
                      | (a_b, (rest_bs, f_b::[]), lift_c) ->
                          let uu___6 =
                            FStar_TypeChecker_Env.uvars_for_binders env
                              rest_bs
                              [FStar_Syntax_Syntax.NT
                                 ((a_b.FStar_Syntax_Syntax.binder_bv), a)]
                              (fun b ->
                                 let uu___7 =
                                   FStar_Syntax_Print.binder_to_string b in
                                 let uu___8 =
                                   FStar_Ident.string_of_lid
                                     ct.FStar_Syntax_Syntax.effect_name in
                                 let uu___9 = FStar_Ident.string_of_lid tgt in
                                 let uu___10 = FStar_Range.string_of_range r in
                                 FStar_Util.format4
                                   "implicit var for binder %s of %s~>%s at %s"
                                   uu___7 uu___8 uu___9 uu___10) r in
                          (match uu___6 with
                           | (rest_bs_uvars, g) ->
                               ((let uu___8 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "LayeredEffects") in
                                 if uu___8
                                 then
                                   let uu___9 =
                                     FStar_List.fold_left
                                       (fun s ->
                                          fun u1 ->
                                            let uu___10 =
                                              let uu___11 =
                                                FStar_Syntax_Print.term_to_string
                                                  u1 in
                                              Prims.op_Hat ";;;;" uu___11 in
                                            Prims.op_Hat s uu___10) ""
                                       rest_bs_uvars in
                                   FStar_Util.print1 "Introduced uvars: %s\n"
                                     uu___9
                                 else ());
                                (let substs =
                                   FStar_List.map2
                                     (fun b ->
                                        fun t ->
                                          FStar_Syntax_Syntax.NT
                                            ((b.FStar_Syntax_Syntax.binder_bv),
                                              t)) (a_b :: rest_bs) (a ::
                                     rest_bs_uvars) in
                                 let guard_f =
                                   let f_sort =
                                     let uu___8 =
                                       FStar_All.pipe_right
                                         (f_b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                                         (FStar_Syntax_Subst.subst substs) in
                                     FStar_All.pipe_right uu___8
                                       FStar_Syntax_Subst.compress in
                                   let f_sort_is =
                                     let uu___8 =
                                       FStar_TypeChecker_Env.is_layered_effect
                                         env
                                         ct.FStar_Syntax_Syntax.effect_name in
                                     effect_args_from_repr f_sort uu___8 r in
                                   FStar_List.fold_left2
                                     (fun g1 ->
                                        fun i1 ->
                                          fun i2 ->
                                            let uu___8 =
                                              FStar_TypeChecker_Rel.layered_effect_teq
                                                env i1 i2
                                                (FStar_Pervasives_Native.Some
                                                   lift_name) in
                                            FStar_TypeChecker_Env.conj_guard
                                              g1 uu___8)
                                     FStar_TypeChecker_Env.trivial_guard c_is
                                     f_sort_is in
                                 let lift_ct =
                                   let uu___8 =
                                     FStar_All.pipe_right lift_c
                                       (FStar_Syntax_Subst.subst_comp substs) in
                                   FStar_All.pipe_right uu___8
                                     FStar_Syntax_Util.comp_to_comp_typ in
                                 let is =
                                   let uu___8 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env tgt in
                                   effect_args_from_repr
                                     lift_ct.FStar_Syntax_Syntax.result_typ
                                     uu___8 r in
                                 let fml =
                                   let uu___8 =
                                     let uu___9 =
                                       FStar_List.hd
                                         lift_ct.FStar_Syntax_Syntax.comp_univs in
                                     let uu___10 =
                                       let uu___11 =
                                         FStar_List.hd
                                           lift_ct.FStar_Syntax_Syntax.effect_args in
                                       FStar_Pervasives_Native.fst uu___11 in
                                     (uu___9, uu___10) in
                                   match uu___8 with
                                   | (u1, wp) ->
                                       FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                         env u1
                                         lift_ct.FStar_Syntax_Syntax.result_typ
                                         wp FStar_Range.dummyRange in
                                 (let uu___9 =
                                    (FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "LayeredEffects"))
                                      &&
                                      (FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme) in
                                  if uu___9
                                  then
                                    let uu___10 =
                                      FStar_Syntax_Print.term_to_string fml in
                                    FStar_Util.print1 "Guard for lift is: %s"
                                      uu___10
                                  else ());
                                 (let c1 =
                                    let uu___9 =
                                      let uu___10 =
                                        FStar_All.pipe_right is
                                          (FStar_List.map
                                             FStar_Syntax_Syntax.as_arg) in
                                      {
                                        FStar_Syntax_Syntax.comp_univs = [u];
                                        FStar_Syntax_Syntax.effect_name = tgt;
                                        FStar_Syntax_Syntax.result_typ = a;
                                        FStar_Syntax_Syntax.effect_args =
                                          uu___10;
                                        FStar_Syntax_Syntax.flags = []
                                      } in
                                    FStar_Syntax_Syntax.mk_Comp uu___9 in
                                  (let uu___10 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "LayeredEffects") in
                                   if uu___10
                                   then
                                     let uu___11 =
                                       FStar_Syntax_Print.comp_to_string c1 in
                                     FStar_Util.print1 "} Lifted comp: %s\n"
                                       uu___11
                                   else ());
                                  (let uu___10 =
                                     let uu___11 =
                                       FStar_TypeChecker_Env.conj_guard g
                                         guard_f in
                                     let uu___12 =
                                       FStar_TypeChecker_Env.guard_of_guard_formula
                                         (FStar_TypeChecker_Common.NonTrivial
                                            fml) in
                                     FStar_TypeChecker_Env.conj_guard uu___11
                                       uu___12 in
                                   (c1, uu___10))))))))))
let lift_tf_layered_effect_term :
  'uuuuu .
    'uuuuu ->
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
              let uu___ =
                let uu___1 =
                  FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift
                    FStar_Util.must in
                FStar_All.pipe_right uu___1
                  (fun ts -> FStar_TypeChecker_Env.inst_tscheme_with ts [u]) in
              FStar_All.pipe_right uu___ FStar_Pervasives_Native.snd in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must in
              let uu___ =
                let uu___1 =
                  let uu___2 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd in
                  FStar_All.pipe_right uu___2 FStar_Syntax_Subst.compress in
                uu___1.FStar_Syntax_Syntax.n in
              match uu___ with
              | FStar_Syntax_Syntax.Tm_arrow (uu___1::bs, uu___2) when
                  (FStar_List.length bs) >= Prims.int_one ->
                  let uu___3 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one)) in
                  FStar_All.pipe_right uu___3 FStar_Pervasives_Native.fst
              | uu___1 ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 =
                        FStar_Syntax_Print.tscheme_to_string lift_t in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu___4 in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu___3) in
                  FStar_Errors.raise_error uu___2
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos in
            let args =
              let uu___ = FStar_Syntax_Syntax.as_arg a in
              let uu___1 =
                let uu___2 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu___3 ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const)) in
                let uu___3 =
                  let uu___4 = FStar_Syntax_Syntax.as_arg e in [uu___4] in
                FStar_List.append uu___2 uu___3 in
              uu___ :: uu___1 in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              e.FStar_Syntax_Syntax.pos
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env ->
    fun datacon ->
      fun index ->
        let uu___ = FStar_TypeChecker_Env.lookup_datacon env datacon in
        match uu___ with
        | (uu___1, t) ->
            let err n =
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_Ident.string_of_lid datacon in
                  let uu___5 = FStar_Util.string_of_int n in
                  let uu___6 = FStar_Util.string_of_int index in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu___4 uu___5 uu___6 in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu___3) in
              let uu___3 = FStar_TypeChecker_Env.get_range env in
              FStar_Errors.raise_error uu___2 uu___3 in
            let uu___2 =
              let uu___3 = FStar_Syntax_Subst.compress t in
              uu___3.FStar_Syntax_Syntax.n in
            (match uu___2 with
             | FStar_Syntax_Syntax.Tm_arrow (bs, uu___3) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu___4 ->
                           match uu___4 with
                           | { FStar_Syntax_Syntax.binder_bv = uu___5;
                               FStar_Syntax_Syntax.binder_qual = q;
                               FStar_Syntax_Syntax.binder_attrs = uu___6;_}
                               ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true)) ->
                                    false
                                | uu___7 -> true))) in
                 if (FStar_List.length bs1) <= index
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index in
                    FStar_Syntax_Util.mk_field_projector_name datacon
                      b.FStar_Syntax_Syntax.binder_bv index)
             | uu___3 -> err Prims.int_zero)
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env ->
    fun sub ->
      let uu___ =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub.FStar_Syntax_Syntax.target) in
      if uu___
      then
        let uu___1 =
          let uu___2 =
            FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must in
          lift_tf_layered_effect sub.FStar_Syntax_Syntax.target uu___2 in
        {
          FStar_TypeChecker_Env.mlift_wp = uu___1;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c in
           check_non_informative_type_for_lift env1
             ct.FStar_Syntax_Syntax.effect_name
             sub.FStar_Syntax_Syntax.target ct.FStar_Syntax_Syntax.result_typ
             env1.FStar_TypeChecker_Env.range;
           (let uu___3 =
              FStar_TypeChecker_Env.inst_tscheme_with ts
                ct.FStar_Syntax_Syntax.comp_univs in
            match uu___3 with
            | (uu___4, lift_t) ->
                let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args in
                let uu___5 =
                  let uu___6 =
                    let uu___7 = ct in
                    let uu___8 =
                      let uu___9 =
                        let uu___10 =
                          let uu___11 =
                            let uu___12 =
                              let uu___13 =
                                let uu___14 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ in
                                [uu___14; wp] in
                              (lift_t, uu___13) in
                            FStar_Syntax_Syntax.Tm_app uu___12 in
                          FStar_Syntax_Syntax.mk uu___11
                            (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos in
                        FStar_All.pipe_right uu___10
                          FStar_Syntax_Syntax.as_arg in
                      [uu___9] in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___7.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        (sub.FStar_Syntax_Syntax.target);
                      FStar_Syntax_Syntax.result_typ =
                        (uu___7.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args = uu___8;
                      FStar_Syntax_Syntax.flags =
                        (uu___7.FStar_Syntax_Syntax.flags)
                    } in
                  FStar_Syntax_Syntax.mk_Comp uu___6 in
                (uu___5, FStar_TypeChecker_Common.trivial_guard)) in
         let mk_mlift_term ts u r e =
           let uu___2 = FStar_TypeChecker_Env.inst_tscheme_with ts [u] in
           match uu___2 with
           | (uu___3, lift_t) ->
               let uu___4 =
                 let uu___5 =
                   let uu___6 =
                     let uu___7 = FStar_Syntax_Syntax.as_arg r in
                     let uu___8 =
                       let uu___9 =
                         FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun in
                       let uu___10 =
                         let uu___11 = FStar_Syntax_Syntax.as_arg e in
                         [uu___11] in
                       uu___9 :: uu___10 in
                     uu___7 :: uu___8 in
                   (lift_t, uu___6) in
                 FStar_Syntax_Syntax.Tm_app uu___5 in
               FStar_Syntax_Syntax.mk uu___4 e.FStar_Syntax_Syntax.pos in
         let uu___2 =
           let uu___3 =
             FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must in
           FStar_All.pipe_right uu___3 mk_mlift_wp in
         {
           FStar_TypeChecker_Env.mlift_wp = uu___2;
           FStar_TypeChecker_Env.mlift_term =
             (match sub.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None ->
                  FStar_Pervasives_Native.Some
                    ((fun uu___3 ->
                        fun uu___4 -> fun e -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff ->
      FStar_Range.range -> FStar_TypeChecker_Env.env)
  =
  fun env ->
    fun sub ->
      fun r ->
        let r0 = env.FStar_TypeChecker_Env.range in
        let env1 =
          let uu___ = get_mlift_for_subeff env sub in
          FStar_TypeChecker_Env.update_effect_lattice
            (let uu___1 = env in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range = r;
               FStar_TypeChecker_Env.curmodule =
                 (uu___1.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.use_eq_strict =
                 (uu___1.FStar_TypeChecker_Env.use_eq_strict);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax = (uu___1.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                 (uu___1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                 (uu___1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___1.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___1.FStar_TypeChecker_Env.try_solve_implicits_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.mpreprocess =
                 (uu___1.FStar_TypeChecker_Env.mpreprocess);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe = (uu___1.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1.FStar_TypeChecker_Env.strict_args_tab);
               FStar_TypeChecker_Env.erasable_types_tab =
                 (uu___1.FStar_TypeChecker_Env.erasable_types_tab);
               FStar_TypeChecker_Env.enable_defer_to_tac =
                 (uu___1.FStar_TypeChecker_Env.enable_defer_to_tac);
               FStar_TypeChecker_Env.unif_allow_ref_guards =
                 (uu___1.FStar_TypeChecker_Env.unif_allow_ref_guards)
             }) sub.FStar_Syntax_Syntax.source sub.FStar_Syntax_Syntax.target
            uu___ in
        let uu___ = env1 in
        {
          FStar_TypeChecker_Env.solver = (uu___.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range = r0;
          FStar_TypeChecker_Env.curmodule =
            (uu___.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma = (uu___.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_sig =
            (uu___.FStar_TypeChecker_Env.gamma_sig);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab = (uu___.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.attrtab =
            (uu___.FStar_TypeChecker_Env.attrtab);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq = (uu___.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.use_eq_strict =
            (uu___.FStar_TypeChecker_Env.use_eq_strict);
          FStar_TypeChecker_Env.is_iface =
            (uu___.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit = (uu___.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax = (uu___.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.phase1 = (uu___.FStar_TypeChecker_Env.phase1);
          FStar_TypeChecker_Env.failhard =
            (uu___.FStar_TypeChecker_Env.failhard);
          FStar_TypeChecker_Env.nosynth =
            (uu___.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.uvar_subtyping =
            (uu___.FStar_TypeChecker_Env.uvar_subtyping);
          FStar_TypeChecker_Env.tc_term =
            (uu___.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
            (uu___.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
          FStar_TypeChecker_Env.universe_of =
            (uu___.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
            (uu___.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.fv_delta_depths =
            (uu___.FStar_TypeChecker_Env.fv_delta_depths);
          FStar_TypeChecker_Env.proof_ns =
            (uu___.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.try_solve_implicits_hook =
            (uu___.FStar_TypeChecker_Env.try_solve_implicits_hook);
          FStar_TypeChecker_Env.splice = (uu___.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.mpreprocess =
            (uu___.FStar_TypeChecker_Env.mpreprocess);
          FStar_TypeChecker_Env.postprocess =
            (uu___.FStar_TypeChecker_Env.postprocess);
          FStar_TypeChecker_Env.identifier_info =
            (uu___.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv = (uu___.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.nbe = (uu___.FStar_TypeChecker_Env.nbe);
          FStar_TypeChecker_Env.strict_args_tab =
            (uu___.FStar_TypeChecker_Env.strict_args_tab);
          FStar_TypeChecker_Env.erasable_types_tab =
            (uu___.FStar_TypeChecker_Env.erasable_types_tab);
          FStar_TypeChecker_Env.enable_defer_to_tac =
            (uu___.FStar_TypeChecker_Env.enable_defer_to_tac);
          FStar_TypeChecker_Env.unif_allow_ref_guards =
            (uu___.FStar_TypeChecker_Env.unif_allow_ref_guards)
        }
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