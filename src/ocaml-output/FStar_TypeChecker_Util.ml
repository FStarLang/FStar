open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option *
    FStar_TypeChecker_Common.lcomp)
let (report : FStar_TypeChecker_Env.env -> Prims.string Prims.list -> unit) =
  fun env  ->
    fun errs  ->
      let uu____22 = FStar_TypeChecker_Env.get_range env  in
      let uu____23 = FStar_TypeChecker_Err.failed_to_prove_specification errs
         in
      FStar_Errors.log_issue uu____22 uu____23
  
let (new_implicit_var :
  Prims.string ->
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.ctx_uvar *
            FStar_Range.range) Prims.list * FStar_TypeChecker_Common.guard_t))
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          FStar_TypeChecker_Env.new_implicit_var_aux reason r env k
            FStar_Syntax_Syntax.Strict FStar_Pervasives_Native.None
  
let (close_guard_implicits :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      FStar_Syntax_Syntax.binders ->
        FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun solve_deferred  ->
      fun xs  ->
        fun g  ->
          let uu____91 = (FStar_Options.eager_subtyping ()) || solve_deferred
             in
          if uu____91
          then
            let uu____94 =
              FStar_All.pipe_right g.FStar_TypeChecker_Common.deferred
                (FStar_List.partition
                   (fun uu____146  ->
                      match uu____146 with
                      | (uu____153,p) ->
                          FStar_TypeChecker_Rel.flex_prob_closing env xs p))
               in
            match uu____94 with
            | (solve_now,defer) ->
                ((let uu____188 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel")
                     in
                  if uu____188
                  then
                    (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                     FStar_List.iter
                       (fun uu____205  ->
                          match uu____205 with
                          | (s,p) ->
                              let uu____215 =
                                FStar_TypeChecker_Rel.prob_to_string env p
                                 in
                              FStar_Util.print2 "%s: %s\n" s uu____215)
                       solve_now;
                     FStar_Util.print_string " ...DEFERRED THE REST:\n";
                     FStar_List.iter
                       (fun uu____230  ->
                          match uu____230 with
                          | (s,p) ->
                              let uu____240 =
                                FStar_TypeChecker_Rel.prob_to_string env p
                                 in
                              FStar_Util.print2 "%s: %s\n" s uu____240) defer;
                     FStar_Util.print_string "END\n")
                  else ());
                 (let g1 =
                    FStar_TypeChecker_Rel.solve_deferred_constraints env
                      (let uu___49_248 = g  in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___49_248.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred = solve_now;
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___49_248.FStar_TypeChecker_Common.univ_ineqs);
                         FStar_TypeChecker_Common.implicits =
                           (uu___49_248.FStar_TypeChecker_Common.implicits)
                       })
                     in
                  let g2 =
                    let uu___52_250 = g1  in
                    {
                      FStar_TypeChecker_Common.guard_f =
                        (uu___52_250.FStar_TypeChecker_Common.guard_f);
                      FStar_TypeChecker_Common.deferred = defer;
                      FStar_TypeChecker_Common.univ_ineqs =
                        (uu___52_250.FStar_TypeChecker_Common.univ_ineqs);
                      FStar_TypeChecker_Common.implicits =
                        (uu___52_250.FStar_TypeChecker_Common.implicits)
                    }  in
                  g2))
          else g
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____267 =
        let uu____269 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____269  in
      if uu____267
      then
        let us =
          let uu____274 =
            let uu____278 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____278
             in
          FStar_All.pipe_right uu____274 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____297 =
            let uu____303 =
              let uu____305 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____305
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____303)  in
          FStar_Errors.log_issue r uu____297);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool))
  =
  fun env  ->
    fun uu____328  ->
      match uu____328 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____339;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____341;
          FStar_Syntax_Syntax.lbpos = uu____342;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____377 = FStar_Syntax_Subst.open_univ_vars univ_vars1 e
                  in
               (match uu____377 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____415) -> aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____422) ->
                          FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____477) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____513 = FStar_Options.ml_ish ()  in
                                if uu____513
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____535 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____535
                            then
                              let uu____538 = FStar_Range.string_of_range r
                                 in
                              let uu____540 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____538 uu____540
                            else ());
                           FStar_Util.Inl t2)
                      | uu____545 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____547 = aux e1  in
                      match uu____547 with
                      | FStar_Util.Inr c ->
                          let uu____553 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____553
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____558 =
                               let uu____564 =
                                 let uu____566 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____566
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____564)
                                in
                             FStar_Errors.raise_error uu____558 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars2, t2, true))
           | uu____575 ->
               let uu____576 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____576 with
                | (univ_vars2,t2) -> (univ_vars2, t2, false)))
  
let rec (decorated_pattern_as_term :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun pat  ->
    let mk1 f =
      FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None
        pat.FStar_Syntax_Syntax.p
       in
    let pat_as_arg uu____640 =
      match uu____640 with
      | (p,i) ->
          let uu____660 = decorated_pattern_as_term p  in
          (match uu____660 with
           | (vars,te) ->
               let uu____683 =
                 let uu____688 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____688)  in
               (vars, uu____683))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____702 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____702)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____706 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____706)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____710 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____710)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____733 =
          let uu____752 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____752 FStar_List.unzip  in
        (match uu____733 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____890 =
               let uu____891 =
                 let uu____892 =
                   let uu____909 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____909, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____892  in
               mk1 uu____891  in
             (vars1, uu____890))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____948,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____958,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____972 -> FStar_Pervasives_Native.Some hd1)
  
let (lcomp_univ_opt :
  FStar_TypeChecker_Common.lcomp ->
    (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option *
      FStar_TypeChecker_Common.guard_t))
  =
  fun lc  ->
    let uu____987 =
      FStar_All.pipe_right lc FStar_TypeChecker_Common.lcomp_comp  in
    FStar_All.pipe_right uu____987
      (fun uu____1015  ->
         match uu____1015 with | (c,g) -> ((comp_univ_opt c), g))
  
let (destruct_wp_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  = fun c  -> FStar_Syntax_Util.destruct_comp c 
let (lift_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp_typ ->
      FStar_TypeChecker_Env.lift_comp_t ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c  ->
      fun lift  ->
        let uu____1082 =
          FStar_All.pipe_right
            (let uu___169_1084 = c  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___169_1084.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___169_1084.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ =
                 (uu___169_1084.FStar_Syntax_Syntax.result_typ);
               FStar_Syntax_Syntax.effect_args =
                 (uu___169_1084.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags = []
             }) FStar_Syntax_Syntax.mk_Comp
           in
        FStar_All.pipe_right uu____1082 (lift env)
  
let (join_layered :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident * FStar_TypeChecker_Env.lift_comp_t *
          FStar_TypeChecker_Env.lift_comp_t))
  =
  fun env  ->
    fun l  ->
      fun m  ->
        let rec aux m1 f_m =
          let uu____1167 = FStar_TypeChecker_Env.join_opt env l m1  in
          match uu____1167 with
          | FStar_Pervasives_Native.None  ->
              let uu____1208 =
                FStar_TypeChecker_Env.lookup_effect_abbrev env
                  [FStar_Syntax_Syntax.U_unknown] m1
                 in
              (match uu____1208 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1245 =
                     let uu____1251 =
                       let uu____1253 = FStar_Syntax_Print.lid_to_string l
                          in
                       let uu____1255 = FStar_Syntax_Print.lid_to_string m1
                          in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____1253
                         uu____1255
                        in
                     (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____1251)
                      in
                   FStar_Errors.raise_error uu____1245
                     env.FStar_TypeChecker_Env.range
               | FStar_Pervasives_Native.Some (uu____1285,c) ->
                   let m2 = FStar_Syntax_Util.comp_effect_name c  in
                   aux m2
                     (fun c1  ->
                        let uu____1295 =
                          let uu____1301 = FStar_All.pipe_right c1 f_m  in
                          FStar_All.pipe_right uu____1301
                            (FStar_TypeChecker_Env.unfold_effect_abbrev_one_step
                               env)
                           in
                        FStar_All.pipe_right uu____1295
                          FStar_Pervasives_Native.fst))
          | FStar_Pervasives_Native.Some (n1,lift1,lift2) ->
              (n1, (lift1.FStar_TypeChecker_Env.mlift_wp),
                ((fun en  ->
                    fun c  ->
                      let uu____1347 = FStar_All.pipe_right c f_m  in
                      FStar_All.pipe_right uu____1347
                        (lift2.FStar_TypeChecker_Env.mlift_wp en))))
           in
        aux m (fun c  -> c)
  
let (join :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident * FStar_TypeChecker_Env.lift_comp_t *
          FStar_TypeChecker_Env.lift_comp_t))
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let unfold_first f en c =
          let uu____1396 =
            let uu____1397 =
              FStar_All.pipe_right c
                (FStar_TypeChecker_Env.unfold_effect_abbrev en)
               in
            FStar_All.pipe_right uu____1397 FStar_Syntax_Syntax.mk_Comp  in
          FStar_All.pipe_right uu____1396 (f en)  in
        let uu____1402 =
          let uu____1407 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____1408 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          (uu____1407, uu____1408)  in
        match uu____1402 with
        | (norm_l1,norm_l2) ->
            let uu____1421 =
              let uu____1428 =
                FStar_TypeChecker_Env.is_layered_effect env norm_l1  in
              let uu____1430 =
                FStar_TypeChecker_Env.is_layered_effect env norm_l2  in
              (uu____1428, uu____1430)  in
            (match uu____1421 with
             | (l1_layered,l2_layered) ->
                 if
                   (l1_layered && l2_layered) ||
                     ((Prims.op_Negation l1_layered) &&
                        (Prims.op_Negation l2_layered))
                 then
                   let uu____1461 =
                     FStar_TypeChecker_Env.join env norm_l1 norm_l2  in
                   (match uu____1461 with
                    | (m,lift1,lift2) ->
                        let uu____1481 =
                          unfold_first lift1.FStar_TypeChecker_Env.mlift_wp
                           in
                        let uu____1486 =
                          unfold_first lift2.FStar_TypeChecker_Env.mlift_wp
                           in
                        (m, uu____1481, uu____1486))
                 else
                   (let uu____1497 =
                      if l1_layered
                      then (norm_l1, l2, false)
                      else (norm_l2, l1, true)  in
                    match uu____1497 with
                    | (norm_l,m,flip) ->
                        let uu____1534 = join_layered env norm_l m  in
                        (match uu____1534 with
                         | (m1,lift1,lift2) ->
                             if flip
                             then
                               let uu____1577 = unfold_first lift1  in
                               (m1, lift2, uu____1577)
                             else
                               (let uu____1588 = unfold_first lift1  in
                                (m1, uu____1588, lift2)))))
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____1613 = join env l1 l2  in
        match uu____1613 with | (m,uu____1625,uu____1626) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____1651 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2)
           in
        if uu____1651
        then FStar_Parser_Const.effect_Tot_lid
        else
          join_effects env c1.FStar_TypeChecker_Common.eff_name
            c2.FStar_TypeChecker_Common.eff_name
  
let (lift_comps :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
          Prims.bool ->
            (FStar_Ident.lident * FStar_Syntax_Syntax.comp *
              FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        fun b  ->
          fun b_maybe_free_in_c2  ->
            let uu____1704 =
              let uu____1709 = FStar_TypeChecker_Env.comp_to_comp_typ env c1
                 in
              let uu____1710 = FStar_TypeChecker_Env.comp_to_comp_typ env c2
                 in
              (uu____1709, uu____1710)  in
            match uu____1704 with
            | (c11,c21) ->
                let uu____1721 =
                  join env c11.FStar_Syntax_Syntax.effect_name
                    c21.FStar_Syntax_Syntax.effect_name
                   in
                (match uu____1721 with
                 | (m,lift1,lift2) ->
                     let uu____1751 = lift_comp env c11 lift1  in
                     (match uu____1751 with
                      | (c12,g1) ->
                          let uu____1766 =
                            if Prims.op_Negation b_maybe_free_in_c2
                            then lift_comp env c21 lift2
                            else
                              (let x_a =
                                 match b with
                                 | FStar_Pervasives_Native.None  ->
                                     FStar_Syntax_Syntax.null_binder
                                       (FStar_Syntax_Util.comp_result c12)
                                 | FStar_Pervasives_Native.Some x ->
                                     FStar_Syntax_Syntax.mk_binder x
                                  in
                               let env_x =
                                 FStar_TypeChecker_Env.push_binders env [x_a]
                                  in
                               let uu____1805 = lift_comp env_x c21 lift2  in
                               match uu____1805 with
                               | (c22,g2) ->
                                   let uu____1816 =
                                     FStar_TypeChecker_Env.close_guard env
                                       [x_a] g2
                                      in
                                   (c22, uu____1816))
                             in
                          (match uu____1766 with
                           | (c22,g2) ->
                               let uu____1839 =
                                 FStar_TypeChecker_Env.conj_guard g1 g2  in
                               (m, c12, c22, uu____1839))))
  
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
          FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun wp  ->
          fun flags  ->
            let uu____1900 =
              let uu____1901 =
                let uu____1912 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____1912]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____1901;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____1900
  
let (mk_comp :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  = fun md  -> mk_comp_l md.FStar_Syntax_Syntax.mname 
let (lax_mk_tot_or_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun flags  ->
          let uu____1996 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____1996
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2008 =
      let uu____2009 = FStar_Syntax_Subst.compress t  in
      uu____2009.FStar_Syntax_Syntax.n  in
    match uu____2008 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2013 -> true
    | uu____2029 -> false
  
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
              let uu____2099 =
                let uu____2101 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____2101  in
              if uu____2099
              then f
              else (let uu____2108 = reason1 ()  in label uu____2108 r f)
  
let (label_guard :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun r  ->
    fun reason  ->
      fun g  ->
        match g.FStar_TypeChecker_Common.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___297_2129 = g  in
            let uu____2130 =
              let uu____2131 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____2131  in
            {
              FStar_TypeChecker_Common.guard_f = uu____2130;
              FStar_TypeChecker_Common.deferred =
                (uu___297_2129.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___297_2129.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___297_2129.FStar_TypeChecker_Common.implicits)
            }
  
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2152 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____2152
        then c
        else
          (let uu____2157 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____2157
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close1 =
                  let uu____2199 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator
                     in
                  FStar_All.pipe_right uu____2199 FStar_Util.must  in
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____2227 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____2227]  in
                       let us =
                         let uu____2249 =
                           let uu____2252 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____2252]  in
                         u_res :: uu____2249  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____2258 =
                         let uu____2263 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md close1
                            in
                         let uu____2264 =
                           let uu____2265 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____2274 =
                             let uu____2285 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____2294 =
                               let uu____2305 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____2305]  in
                             uu____2285 :: uu____2294  in
                           uu____2265 :: uu____2274  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2263 uu____2264
                          in
                       uu____2258 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____2347 = destruct_wp_comp c1  in
              match uu____2347 with
              | (u_res_t,res_t,wp) ->
                  let md =
                    FStar_TypeChecker_Env.get_effect_decl env
                      c1.FStar_Syntax_Syntax.effect_name
                     in
                  let wp1 = close_wp u_res_t md res_t bvs wp  in
                  mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1
                    c1.FStar_Syntax_Syntax.flags))
  
let (close_wp_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun bvs  ->
      fun lc  ->
        let bs =
          FStar_All.pipe_right bvs
            (FStar_List.map FStar_Syntax_Syntax.mk_binder)
           in
        FStar_All.pipe_right lc
          (FStar_TypeChecker_Common.apply_lcomp (close_wp_comp env bvs)
             (fun g  ->
                let uu____2387 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____2387
                  (close_guard_implicits env false bs)))
  
let (close_layered_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.term Prims.list ->
        FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun bvs  ->
      fun tms  ->
        fun lc  ->
          let bs =
            FStar_All.pipe_right bvs
              (FStar_List.map FStar_Syntax_Syntax.mk_binder)
             in
          let substs =
            FStar_List.map2
              (fun bv  -> fun tm  -> FStar_Syntax_Syntax.NT (bv, tm)) bvs tms
             in
          FStar_All.pipe_right lc
            (FStar_TypeChecker_Common.apply_lcomp
               (FStar_Syntax_Subst.subst_comp substs)
               (fun g  ->
                  let uu____2437 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs)
                     in
                  FStar_All.pipe_right uu____2437
                    (close_guard_implicits env false bs)))
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_2450  ->
            match uu___0_2450 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____2453 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____2478 =
            let uu____2481 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____2481 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____2478
            (fun c  ->
               (let uu____2537 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____2537) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____2541 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____2541)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____2552 = FStar_Syntax_Util.head_and_args' e  in
                match uu____2552 with
                | (head1,uu____2569) ->
                    let uu____2590 =
                      let uu____2591 = FStar_Syntax_Util.un_uinst head1  in
                      uu____2591.FStar_Syntax_Syntax.n  in
                    (match uu____2590 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2596 =
                           let uu____2598 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____2598
                            in
                         Prims.op_Negation uu____2596
                     | uu____2599 -> true)))
              &&
              (let uu____2602 = should_not_inline_lc lc  in
               Prims.op_Negation uu____2602)
  
let (return_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun u_t_opt  ->
      fun t  ->
        fun v1  ->
          let c =
            let uu____2630 =
              let uu____2632 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____2632  in
            if uu____2630
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____2639 = FStar_Syntax_Util.is_unit t  in
               if uu____2639
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
                    let uu____2648 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____2648
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____2653 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____2653 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let ret_wp =
                             FStar_All.pipe_right m
                               FStar_Syntax_Util.get_return_vc_combinator
                              in
                           let uu____2664 =
                             let uu____2665 =
                               let uu____2670 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m ret_wp
                                  in
                               let uu____2671 =
                                 let uu____2672 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____2681 =
                                   let uu____2692 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____2692]  in
                                 uu____2672 :: uu____2681  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____2670
                                 uu____2671
                                in
                             uu____2665 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____2664)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____2726 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____2726
           then
             let uu____2731 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____2733 = FStar_Syntax_Print.term_to_string v1  in
             let uu____2735 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____2731 uu____2733 uu____2735
           else ());
          c
  
let (mk_layered_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.comp_typ ->
        FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
          FStar_Syntax_Syntax.comp_typ ->
            FStar_Syntax_Syntax.cflag Prims.list ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun m  ->
      fun ct1  ->
        fun b  ->
          fun ct2  ->
            fun flags  ->
              fun r1  ->
                (let uu____2793 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____2793
                 then
                   let uu____2798 =
                     let uu____2800 = FStar_Syntax_Syntax.mk_Comp ct1  in
                     FStar_Syntax_Print.comp_to_string uu____2800  in
                   let uu____2801 =
                     let uu____2803 = FStar_Syntax_Syntax.mk_Comp ct2  in
                     FStar_Syntax_Print.comp_to_string uu____2803  in
                   FStar_Util.print2 "Binding c1:%s and c2:%s {\n" uu____2798
                     uu____2801
                 else ());
                (let ed = FStar_TypeChecker_Env.get_effect_decl env m  in
                 let uu____2808 =
                   let uu____2819 =
                     FStar_List.hd ct1.FStar_Syntax_Syntax.comp_univs  in
                   let uu____2820 =
                     FStar_List.map FStar_Pervasives_Native.fst
                       ct1.FStar_Syntax_Syntax.effect_args
                      in
                   (uu____2819, (ct1.FStar_Syntax_Syntax.result_typ),
                     uu____2820)
                    in
                 match uu____2808 with
                 | (u1,t1,is1) ->
                     let uu____2854 =
                       let uu____2865 =
                         FStar_List.hd ct2.FStar_Syntax_Syntax.comp_univs  in
                       let uu____2866 =
                         FStar_List.map FStar_Pervasives_Native.fst
                           ct2.FStar_Syntax_Syntax.effect_args
                          in
                       (uu____2865, (ct2.FStar_Syntax_Syntax.result_typ),
                         uu____2866)
                        in
                     (match uu____2854 with
                      | (u2,t2,is2) ->
                          let uu____2900 =
                            let uu____2905 =
                              FStar_All.pipe_right ed
                                FStar_Syntax_Util.get_bind_vc_combinator
                               in
                            FStar_TypeChecker_Env.inst_tscheme_with
                              uu____2905 [u1; u2]
                             in
                          (match uu____2900 with
                           | (uu____2910,bind_t) ->
                               let bind_t_shape_error s =
                                 let uu____2925 =
                                   let uu____2927 =
                                     FStar_Syntax_Print.term_to_string bind_t
                                      in
                                   FStar_Util.format2
                                     "bind %s does not have proper shape (reason:%s)"
                                     uu____2927 s
                                    in
                                 (FStar_Errors.Fatal_UnexpectedEffect,
                                   uu____2925)
                                  in
                               let uu____2931 =
                                 let uu____2976 =
                                   let uu____2977 =
                                     FStar_Syntax_Subst.compress bind_t  in
                                   uu____2977.FStar_Syntax_Syntax.n  in
                                 match uu____2976 with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (4))
                                     ->
                                     let uu____3053 =
                                       FStar_Syntax_Subst.open_comp bs c  in
                                     (match uu____3053 with
                                      | (a_b::b_b::bs1,c1) ->
                                          let uu____3138 =
                                            let uu____3165 =
                                              FStar_List.splitAt
                                                ((FStar_List.length bs1) -
                                                   (Prims.of_int (2))) bs1
                                               in
                                            FStar_All.pipe_right uu____3165
                                              (fun uu____3250  ->
                                                 match uu____3250 with
                                                 | (l1,l2) ->
                                                     let uu____3331 =
                                                       FStar_List.hd l2  in
                                                     let uu____3344 =
                                                       let uu____3351 =
                                                         FStar_List.tl l2  in
                                                       FStar_List.hd
                                                         uu____3351
                                                        in
                                                     (l1, uu____3331,
                                                       uu____3344))
                                             in
                                          (match uu____3138 with
                                           | (rest_bs,f_b,g_b) ->
                                               let uu____3479 =
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                   c1
                                                  in
                                               (a_b, b_b, rest_bs, f_b, g_b,
                                                 uu____3479)))
                                 | uu____3512 ->
                                     let uu____3513 =
                                       bind_t_shape_error
                                         "Either not an arrow or not enough binders"
                                        in
                                     FStar_Errors.raise_error uu____3513 r1
                                  in
                               (match uu____2931 with
                                | (a_b,b_b,rest_bs,f_b,g_b,bind_ct) ->
                                    let uu____3638 =
                                      let uu____3645 =
                                        let uu____3646 =
                                          let uu____3647 =
                                            let uu____3654 =
                                              FStar_All.pipe_right a_b
                                                FStar_Pervasives_Native.fst
                                               in
                                            (uu____3654, t1)  in
                                          FStar_Syntax_Syntax.NT uu____3647
                                           in
                                        let uu____3665 =
                                          let uu____3668 =
                                            let uu____3669 =
                                              let uu____3676 =
                                                FStar_All.pipe_right b_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____3676, t2)  in
                                            FStar_Syntax_Syntax.NT uu____3669
                                             in
                                          [uu____3668]  in
                                        uu____3646 :: uu____3665  in
                                      FStar_TypeChecker_Env.uvars_for_binders
                                        env rest_bs uu____3645
                                        (fun b1  ->
                                           let uu____3691 =
                                             FStar_Syntax_Print.binder_to_string
                                               b1
                                              in
                                           let uu____3693 =
                                             FStar_Range.string_of_range r1
                                              in
                                           FStar_Util.format3
                                             "implicit var for binder %s of %s:bind at %s"
                                             uu____3691
                                             (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                             uu____3693) r1
                                       in
                                    (match uu____3638 with
                                     | (rest_bs_uvars,g_uvars) ->
                                         let subst1 =
                                           FStar_List.map2
                                             (fun b1  ->
                                                fun t  ->
                                                  let uu____3730 =
                                                    let uu____3737 =
                                                      FStar_All.pipe_right b1
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    (uu____3737, t)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____3730) (a_b :: b_b
                                             :: rest_bs) (t1 :: t2 ::
                                             rest_bs_uvars)
                                            in
                                         let f_guard =
                                           let f_sort_is =
                                             let uu____3764 =
                                               let uu____3765 =
                                                 let uu____3768 =
                                                   let uu____3769 =
                                                     FStar_All.pipe_right f_b
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   uu____3769.FStar_Syntax_Syntax.sort
                                                    in
                                                 FStar_Syntax_Subst.compress
                                                   uu____3768
                                                  in
                                               uu____3765.FStar_Syntax_Syntax.n
                                                in
                                             match uu____3764 with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____3780,uu____3781::is)
                                                 ->
                                                 let uu____3823 =
                                                   FStar_All.pipe_right is
                                                     (FStar_List.map
                                                        FStar_Pervasives_Native.fst)
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3823
                                                   (FStar_List.map
                                                      (FStar_Syntax_Subst.subst
                                                         subst1))
                                             | uu____3856 ->
                                                 let uu____3857 =
                                                   bind_t_shape_error
                                                     "f's type is not a repr type"
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____3857 r1
                                              in
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun i1  ->
                                                  fun f_i1  ->
                                                    let uu____3873 =
                                                      FStar_TypeChecker_Rel.teq
                                                        env i1 f_i1
                                                       in
                                                    FStar_TypeChecker_Env.conj_guard
                                                      g uu____3873)
                                             FStar_TypeChecker_Env.trivial_guard
                                             is1 f_sort_is
                                            in
                                         let g_guard =
                                           let x_a =
                                             match b with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Syntax_Syntax.null_binder
                                                   ct1.FStar_Syntax_Syntax.result_typ
                                             | FStar_Pervasives_Native.Some x
                                                 ->
                                                 FStar_Syntax_Syntax.mk_binder
                                                   x
                                              in
                                           let g_sort_is =
                                             let uu____3892 =
                                               let uu____3893 =
                                                 let uu____3896 =
                                                   let uu____3897 =
                                                     FStar_All.pipe_right g_b
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   uu____3897.FStar_Syntax_Syntax.sort
                                                    in
                                                 FStar_Syntax_Subst.compress
                                                   uu____3896
                                                  in
                                               uu____3893.FStar_Syntax_Syntax.n
                                                in
                                             match uu____3892 with
                                             | FStar_Syntax_Syntax.Tm_arrow
                                                 (bs,c) ->
                                                 let uu____3930 =
                                                   FStar_Syntax_Subst.open_comp
                                                     bs c
                                                    in
                                                 (match uu____3930 with
                                                  | (bs1,c1) ->
                                                      let bs_subst =
                                                        let uu____3940 =
                                                          let uu____3947 =
                                                            let uu____3948 =
                                                              FStar_List.hd
                                                                bs1
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____3948
                                                              FStar_Pervasives_Native.fst
                                                             in
                                                          let uu____3969 =
                                                            let uu____3972 =
                                                              FStar_All.pipe_right
                                                                x_a
                                                                FStar_Pervasives_Native.fst
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____3972
                                                              FStar_Syntax_Syntax.bv_to_name
                                                             in
                                                          (uu____3947,
                                                            uu____3969)
                                                           in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____3940
                                                         in
                                                      let c2 =
                                                        FStar_Syntax_Subst.subst_comp
                                                          [bs_subst] c1
                                                         in
                                                      let uu____3986 =
                                                        let uu____3987 =
                                                          FStar_Syntax_Subst.compress
                                                            (FStar_Syntax_Util.comp_result
                                                               c2)
                                                           in
                                                        uu____3987.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____3986 with
                                                       | FStar_Syntax_Syntax.Tm_app
                                                           (uu____3992,uu____3993::is)
                                                           ->
                                                           let uu____4035 =
                                                             FStar_All.pipe_right
                                                               is
                                                               (FStar_List.map
                                                                  FStar_Pervasives_Native.fst)
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____4035
                                                             (FStar_List.map
                                                                (FStar_Syntax_Subst.subst
                                                                   subst1))
                                                       | uu____4068 ->
                                                           let uu____4069 =
                                                             bind_t_shape_error
                                                               "g's type is not a repr type"
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4069 r1))
                                             | uu____4078 ->
                                                 let uu____4079 =
                                                   bind_t_shape_error
                                                     "g's type is not an arrow"
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____4079 r1
                                              in
                                           let env_g =
                                             FStar_TypeChecker_Env.push_binders
                                               env [x_a]
                                              in
                                           let uu____4101 =
                                             FStar_List.fold_left2
                                               (fun g  ->
                                                  fun i1  ->
                                                    fun g_i1  ->
                                                      let uu____4109 =
                                                        FStar_TypeChecker_Rel.teq
                                                          env_g i1 g_i1
                                                         in
                                                      FStar_TypeChecker_Env.conj_guard
                                                        g uu____4109)
                                               FStar_TypeChecker_Env.trivial_guard
                                               is2 g_sort_is
                                              in
                                           FStar_All.pipe_right uu____4101
                                             (FStar_TypeChecker_Env.close_guard
                                                env [x_a])
                                            in
                                         let is =
                                           let uu____4125 =
                                             let uu____4126 =
                                               FStar_Syntax_Subst.compress
                                                 bind_ct.FStar_Syntax_Syntax.result_typ
                                                in
                                             uu____4126.FStar_Syntax_Syntax.n
                                              in
                                           match uu____4125 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____4131,uu____4132::is) ->
                                               let uu____4174 =
                                                 FStar_All.pipe_right is
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_All.pipe_right
                                                 uu____4174
                                                 (FStar_List.map
                                                    (FStar_Syntax_Subst.subst
                                                       subst1))
                                           | uu____4207 ->
                                               let uu____4208 =
                                                 bind_t_shape_error
                                                   "return type is not a repr type"
                                                  in
                                               FStar_Errors.raise_error
                                                 uu____4208 r1
                                            in
                                         let c =
                                           let uu____4218 =
                                             let uu____4219 =
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 is
                                                in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 =
                                                 (ct2.FStar_Syntax_Syntax.comp_univs);
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = t2;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____4219;
                                               FStar_Syntax_Syntax.flags =
                                                 flags
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____4218
                                            in
                                         ((let uu____4239 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env)
                                               (FStar_Options.Other
                                                  "LayeredEffects")
                                              in
                                           if uu____4239
                                           then
                                             let uu____4244 =
                                               FStar_Syntax_Print.comp_to_string
                                                 c
                                                in
                                             FStar_Util.print1
                                               "} c after bind: %s\n"
                                               uu____4244
                                           else ());
                                          (let uu____4249 =
                                             FStar_TypeChecker_Env.conj_guards
                                               [g_uvars; f_guard; g_guard]
                                              in
                                           (c, uu____4249))))))))
  
let (mk_non_layered_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.comp_typ ->
        FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
          FStar_Syntax_Syntax.comp_typ ->
            FStar_Syntax_Syntax.cflag Prims.list ->
              FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun m  ->
      fun ct1  ->
        fun b  ->
          fun ct2  ->
            fun flags  ->
              fun r1  ->
                let uu____4294 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____4320 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____4320 with
                  | (a,kwp) ->
                      let uu____4351 = destruct_wp_comp ct1  in
                      let uu____4358 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____4351, uu____4358)
                   in
                match uu____4294 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____4411 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____4411]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____4431 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____4431]
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
                      let uu____4478 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____4487 =
                        let uu____4498 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____4507 =
                          let uu____4518 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____4527 =
                            let uu____4538 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____4547 =
                              let uu____4558 =
                                let uu____4567 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____4567  in
                              [uu____4558]  in
                            uu____4538 :: uu____4547  in
                          uu____4518 :: uu____4527  in
                        uu____4498 :: uu____4507  in
                      uu____4478 :: uu____4487  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____4620 =
                        let uu____4625 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_t1; u_t2] env md bind_wp
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____4625 wp_args  in
                      uu____4620 FStar_Pervasives_Native.None
                        t2.FStar_Syntax_Syntax.pos
                       in
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
  fun env  ->
    fun c1  ->
      fun b  ->
        fun c2  ->
          fun flags  ->
            fun r1  ->
              let uu____4673 = lift_comps env c1 c2 b true  in
              match uu____4673 with
              | (m,c11,c21,g_lift) ->
                  let uu____4691 =
                    let uu____4696 = FStar_Syntax_Util.comp_to_comp_typ c11
                       in
                    let uu____4697 = FStar_Syntax_Util.comp_to_comp_typ c21
                       in
                    (uu____4696, uu____4697)  in
                  (match uu____4691 with
                   | (ct1,ct2) ->
                       let uu____4704 =
                         let uu____4709 =
                           FStar_TypeChecker_Env.is_layered_effect env m  in
                         if uu____4709
                         then mk_layered_bind env m ct1 b ct2 flags r1
                         else
                           (let uu____4718 =
                              mk_non_layered_bind env m ct1 b ct2 flags r1
                               in
                            (uu____4718, FStar_TypeChecker_Env.trivial_guard))
                          in
                       (match uu____4704 with
                        | (c,g_bind) ->
                            let uu____4725 =
                              FStar_TypeChecker_Env.conj_guard g_lift g_bind
                               in
                            (c, uu____4725)))
  
let (bind_pure_wp_with :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.cflag Prims.list ->
          (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun wp1  ->
      fun c  ->
        fun flags  ->
          let r = FStar_TypeChecker_Env.get_range env  in
          let pure_c =
            let uu____4761 =
              let uu____4762 =
                let uu____4773 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____4773]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____4762;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4761  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____4818 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_4824  ->
              match uu___1_4824 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____4827 -> false))
       in
    if uu____4818
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_4839  ->
              match uu___2_4839 with
              | FStar_Syntax_Syntax.TOTAL  ->
                  [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | FStar_Syntax_Syntax.RETURN  ->
                  [FStar_Syntax_Syntax.PARTIAL_RETURN;
                  FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | f -> [f]))
  
let (weaken_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c  ->
      fun formula  ->
        let uu____4867 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4867
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____4878 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____4878  in
           let pure_assume_wp1 =
             let uu____4883 = FStar_TypeChecker_Env.get_range env  in
             let uu____4884 =
               let uu____4889 =
                 let uu____4890 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____4890]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____4889  in
             uu____4884 FStar_Pervasives_Native.None uu____4883  in
           let uu____4923 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____4923)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____4951 =
          let uu____4952 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____4952 with
          | (c,g_c) ->
              let uu____4963 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____4963
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____4977 = weaken_comp env c f1  in
                     (match uu____4977 with
                      | (c1,g_w) ->
                          let uu____4988 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____4988)))
           in
        let uu____4989 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____4989 weaken
  
let (strengthen_comp :
  FStar_TypeChecker_Env.env ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.formula ->
          FStar_Syntax_Syntax.cflag Prims.list ->
            (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun reason  ->
      fun c  ->
        fun f  ->
          fun flags  ->
            if env.FStar_TypeChecker_Env.lax
            then (c, FStar_TypeChecker_Env.trivial_guard)
            else
              (let r = FStar_TypeChecker_Env.get_range env  in
               let pure_assert_wp =
                 let uu____5046 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____5046  in
               let pure_assert_wp1 =
                 let uu____5051 =
                   let uu____5056 =
                     let uu____5057 =
                       let uu____5066 = label_opt env reason r f  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                         uu____5066
                        in
                     [uu____5057]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____5056
                    in
                 uu____5051 FStar_Pervasives_Native.None r  in
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
  fun reason  ->
    fun env  ->
      fun e_for_debugging_only  ->
        fun lc  ->
          fun g0  ->
            let uu____5136 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____5136
            then (lc, g0)
            else
              (let flags =
                 let uu____5148 =
                   let uu____5156 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____5156
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5148 with
                 | (maybe_trivial_post,flags) ->
                     let uu____5186 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_5194  ->
                               match uu___3_5194 with
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
                               | uu____5197 -> []))
                        in
                     FStar_List.append flags uu____5186
                  in
               let strengthen uu____5207 =
                 let uu____5208 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____5208 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____5227 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____5227 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____5234 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____5234
                              then
                                let uu____5238 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____5240 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____5238 uu____5240
                              else ());
                             (let uu____5245 =
                                strengthen_comp env reason c f flags  in
                              match uu____5245 with
                              | (c1,g_s) ->
                                  let uu____5256 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____5256))))
                  in
               let uu____5257 =
                 let uu____5258 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____5258
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____5257,
                 (let uu___613_5260 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___613_5260.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___613_5260.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___613_5260.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_5269  ->
            match uu___4_5269 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____5273 -> false) lc.FStar_TypeChecker_Common.cflags)
  
let (maybe_add_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun uopt  ->
      fun lc  ->
        fun e  ->
          let uu____5302 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____5302
          then e
          else
            (let uu____5309 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____5312 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____5312)
                in
             if uu____5309
             then
               let u =
                 match uopt with
                 | FStar_Pervasives_Native.Some u -> u
                 | FStar_Pervasives_Native.None  ->
                     env.FStar_TypeChecker_Env.universe_of env
                       lc.FStar_TypeChecker_Common.res_typ
                  in
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
  fun env  ->
    fun t  ->
      fun x  ->
        fun c  ->
          let t1 =
            FStar_TypeChecker_Normalize.normalize_refinement
              FStar_TypeChecker_Normalize.whnf_steps env t
             in
          match t1.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (b,phi) ->
              let is_unit1 =
                match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.unit_lid
                | uu____5382 -> false  in
              if is_unit1
              then
                let uu____5389 =
                  let uu____5391 =
                    let uu____5392 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____5392
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____5391
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____5389
                 then
                   let uu____5401 =
                     FStar_Syntax_Subst.open_term
                       [(b, FStar_Pervasives_Native.None)] phi
                      in
                   match uu____5401 with
                   | (b1::[],phi1) ->
                       let phi2 =
                         let uu____5445 =
                           let uu____5448 =
                             let uu____5449 =
                               let uu____5456 =
                                 FStar_All.pipe_right b1
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____5456, FStar_Syntax_Syntax.unit_const)
                                in
                             FStar_Syntax_Syntax.NT uu____5449  in
                           [uu____5448]  in
                         FStar_Syntax_Subst.subst uu____5445 phi1  in
                       weaken_comp env c phi2
                 else
                   (let uu____5469 = close_wp_comp env [x] c  in
                    (uu____5469, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____5472 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
let (bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Common.lcomp ->
          lcomp_with_binder -> FStar_TypeChecker_Common.lcomp)
  =
  fun r1  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun uu____5500  ->
            match uu____5500 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____5520 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____5520 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____5533 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____5533
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____5543 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____5543
                       then
                         let uu____5548 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____5548
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5555 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____5555
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5564 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____5564
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____5571 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____5571
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____5587 =
                  let uu____5588 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____5588
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____5596 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____5596, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____5599 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____5599 with
                     | (c1,g_c1) ->
                         let uu____5610 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____5610 with
                          | (c2,g_c2) ->
                              (debug1
                                 (fun uu____5630  ->
                                    let uu____5631 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____5633 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____5638 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____5631 uu____5633 uu____5638);
                               (let aux uu____5656 =
                                  let uu____5657 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____5657
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____5688
                                        ->
                                        let uu____5689 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____5689
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____5721 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____5721
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____5768 =
                                  let aux_with_trivial_guard uu____5798 =
                                    let uu____5799 = aux ()  in
                                    match uu____5799 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c,
                                            FStar_TypeChecker_Env.trivial_guard,
                                            reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____5857 =
                                    let uu____5859 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____5859  in
                                  if uu____5857
                                  then
                                    let uu____5875 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____5875
                                     then
                                       FStar_Util.Inl
                                         (c2,
                                           FStar_TypeChecker_Env.trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____5902 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____5902))
                                  else
                                    (let uu____5919 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____5919
                                     then
                                       let close1 x reason c =
                                         let x1 =
                                           let uu___712_5965 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___712_5965.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___712_5965.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           }  in
                                         let uu____5966 =
                                           maybe_capture_unit_refinement env
                                             x1.FStar_Syntax_Syntax.sort x1 c
                                            in
                                         match uu____5966 with
                                         | (c3,g_c) ->
                                             FStar_Util.Inl (c3, g_c, reason)
                                          in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some
                                          e,FStar_Pervasives_Native.Some x)
                                           ->
                                           let uu____6024 =
                                             FStar_All.pipe_right c2
                                               (FStar_Syntax_Subst.subst_comp
                                                  [FStar_Syntax_Syntax.NT
                                                     (x, e)])
                                              in
                                           FStar_All.pipe_right uu____6024
                                             (close1 x "c1 Tot")
                                       | (uu____6040,FStar_Pervasives_Native.Some
                                          x) ->
                                           FStar_All.pipe_right c2
                                             (close1 x "c1 Tot only close")
                                       | (uu____6065,uu____6066) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____6081 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____6081
                                        then
                                          let uu____6096 =
                                            let uu____6104 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____6104,
                                              FStar_TypeChecker_Env.trivial_guard,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____6096
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____6117 = try_simplify ()  in
                                match uu____6117 with
                                | FStar_Util.Inl (c,g_c,reason) ->
                                    (debug1
                                       (fun uu____6152  ->
                                          let uu____6153 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____6153);
                                     (let uu____6156 =
                                        let uu____6157 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_c1 g_c2
                                           in
                                        FStar_TypeChecker_Env.conj_guard g_c
                                          uu____6157
                                         in
                                      (c, uu____6156)))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____6171  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 =
                                        let uu____6197 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____6197 with
                                        | (c,g_bind) ->
                                            let uu____6208 =
                                              let uu____6209 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g_c1 g_c2
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                uu____6209 g_bind
                                               in
                                            (c, uu____6208)
                                         in
                                      let mk_seq c11 b1 c21 =
                                        let uu____6234 =
                                          let uu____6239 =
                                            FStar_TypeChecker_Env.comp_to_comp_typ
                                              env c11
                                             in
                                          let uu____6240 =
                                            FStar_TypeChecker_Env.comp_to_comp_typ
                                              env c21
                                             in
                                          (uu____6239, uu____6240)  in
                                        match uu____6234 with
                                        | (c12,c22) ->
                                            let uu____6247 =
                                              join env
                                                c12.FStar_Syntax_Syntax.effect_name
                                                c22.FStar_Syntax_Syntax.effect_name
                                               in
                                            (match uu____6247 with
                                             | (m,uu____6263,lift2) ->
                                                 let uu____6273 =
                                                   lift_comp env c22 lift2
                                                    in
                                                 (match uu____6273 with
                                                  | (c23,g2) ->
                                                      let uu____6284 =
                                                        destruct_wp_comp c12
                                                         in
                                                      (match uu____6284 with
                                                       | (u1,t1,wp1) ->
                                                           let md_pure_or_ghost
                                                             =
                                                             FStar_TypeChecker_Env.get_effect_decl
                                                               env
                                                               c12.FStar_Syntax_Syntax.effect_name
                                                              in
                                                           let trivial =
                                                             let uu____6300 =
                                                               FStar_All.pipe_right
                                                                 md_pure_or_ghost
                                                                 FStar_Syntax_Util.get_wp_trivial_combinator
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____6300
                                                               FStar_Util.must
                                                              in
                                                           let vc1 =
                                                             let uu____6310 =
                                                               let uu____6315
                                                                 =
                                                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                                                   [u1] env
                                                                   md_pure_or_ghost
                                                                   trivial
                                                                  in
                                                               let uu____6316
                                                                 =
                                                                 let uu____6317
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    t1
                                                                    in
                                                                 let uu____6326
                                                                   =
                                                                   let uu____6337
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp1  in
                                                                   [uu____6337]
                                                                    in
                                                                 uu____6317
                                                                   ::
                                                                   uu____6326
                                                                  in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____6315
                                                                 uu____6316
                                                                in
                                                             uu____6310
                                                               FStar_Pervasives_Native.None
                                                               r1
                                                              in
                                                           let uu____6370 =
                                                             strengthen_comp
                                                               env
                                                               FStar_Pervasives_Native.None
                                                               c23 vc1
                                                               bind_flags
                                                              in
                                                           (match uu____6370
                                                            with
                                                            | (c,g_s) ->
                                                                let uu____6385
                                                                  =
                                                                  FStar_TypeChecker_Env.conj_guards
                                                                    [g_c1;
                                                                    g_c2;
                                                                    g2;
                                                                    g_s]
                                                                   in
                                                                (c,
                                                                  uu____6385)))))
                                         in
                                      let uu____6386 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____6402 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____6402, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____6386 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____6418 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____6418
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____6427 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____6427
                                             then
                                               (debug1
                                                  (fun uu____6441  ->
                                                     let uu____6442 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____6444 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____6442 uu____6444);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 mk_bind1 c1 b c21))
                                             else
                                               (let uu____6452 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____6455 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____6455)
                                                   in
                                                if uu____6452
                                                then
                                                  let e1' =
                                                    let uu____6480 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____6480
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug1
                                                     (fun uu____6492  ->
                                                        let uu____6493 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____6495 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____6493
                                                          uu____6495);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug1
                                                     (fun uu____6510  ->
                                                        let uu____6511 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____6513 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____6511
                                                          uu____6513);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____6520 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____6520
                                                       in
                                                    let uu____6521 =
                                                      let uu____6526 =
                                                        let uu____6527 =
                                                          let uu____6528 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____6528]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____6527
                                                         in
                                                      weaken_comp uu____6526
                                                        c21 x_eq_e
                                                       in
                                                    match uu____6521 with
                                                    | (c22,g_w) ->
                                                        let uu____6553 =
                                                          mk_bind1 c1 b c22
                                                           in
                                                        (match uu____6553
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____6564 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____6564))))))
                                          else mk_bind1 c1 b c2))))))
                   in
                FStar_TypeChecker_Common.mk_lcomp joined_eff
                  lc21.FStar_TypeChecker_Common.res_typ bind_flags bind_it
  
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
      | uu____6581 -> g2
  
let (maybe_assume_result_eq_pure_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
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
            (let uu____6605 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____6605)
           in
        let flags =
          if should_return1
          then
            let uu____6613 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____6613
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____6631 =
          let uu____6632 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____6632 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____6645 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____6645
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____6653 =
                  let uu____6655 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____6655  in
                (if uu____6653
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___832_6664 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___832_6664.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___832_6664.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___832_6664.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____6665 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____6665, g_c)
                 else
                   (let uu____6668 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____6668, g_c)))
              else
                (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c
                    in
                 let t = c1.FStar_Syntax_Syntax.result_typ  in
                 let c2 = FStar_Syntax_Syntax.mk_Comp c1  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (t.FStar_Syntax_Syntax.pos)) t
                    in
                 let xexp = FStar_Syntax_Syntax.bv_to_name x  in
                 let ret1 =
                   let uu____6679 =
                     let uu____6680 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____6680
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____6679
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____6683 =
                   let uu____6688 =
                     let uu____6689 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____6689
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____6688  in
                 match uu____6683 with
                 | (bind_c,g_bind) ->
                     let uu____6698 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____6699 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____6698, uu____6699))
           in
        if Prims.op_Negation should_return1
        then lc
        else
          FStar_TypeChecker_Common.mk_lcomp
            lc.FStar_TypeChecker_Common.eff_name
            lc.FStar_TypeChecker_Common.res_typ flags refine1
  
let (maybe_return_e2_and_bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Common.lcomp ->
          FStar_Syntax_Syntax.term ->
            lcomp_with_binder -> FStar_TypeChecker_Common.lcomp)
  =
  fun r  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun e2  ->
            fun uu____6735  ->
              match uu____6735 with
              | (x,lc2) ->
                  let lc21 =
                    let eff1 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc1.FStar_TypeChecker_Common.eff_name
                       in
                    let eff2 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc2.FStar_TypeChecker_Common.eff_name
                       in
                    let uu____6747 =
                      ((let uu____6751 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____6751) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____6747
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6769 =
        let uu____6770 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6770  in
      FStar_Syntax_Syntax.fvar uu____6769 FStar_Syntax_Syntax.delta_constant
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
  fun env  ->
    fun ed  ->
      fun u_a  ->
        fun a  ->
          fun p  ->
            fun ct1  ->
              fun ct2  ->
                fun r  ->
                  let uu____6820 =
                    let uu____6825 =
                      let uu____6826 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____6826 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____6825 [u_a]
                     in
                  match uu____6820 with
                  | (uu____6837,conjunction) ->
                      let uu____6839 =
                        let uu____6848 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____6863 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____6848, uu____6863)  in
                      (match uu____6839 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____6909 =
                               let uu____6911 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____6911 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____6909)
                              in
                           let uu____6915 =
                             let uu____6960 =
                               let uu____6961 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____6961.FStar_Syntax_Syntax.n  in
                             match uu____6960 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____7010) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____7042 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____7042 with
                                  | (a_b::bs1,body1) ->
                                      let uu____7114 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____7114 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____7262 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____7262)))
                             | uu____7295 ->
                                 let uu____7296 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____7296 r
                              in
                           (match uu____6915 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____7421 =
                                  let uu____7428 =
                                    let uu____7429 =
                                      let uu____7430 =
                                        let uu____7437 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____7437, a)  in
                                      FStar_Syntax_Syntax.NT uu____7430  in
                                    [uu____7429]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____7428
                                    (fun b  ->
                                       let uu____7453 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____7455 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____7457 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____7453 uu____7455 uu____7457) r
                                   in
                                (match uu____7421 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____7495 =
                                                let uu____7502 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____7502, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____7495) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____7541 =
                                           let uu____7542 =
                                             let uu____7545 =
                                               let uu____7546 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____7546.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____7545
                                              in
                                           uu____7542.FStar_Syntax_Syntax.n
                                            in
                                         match uu____7541 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____7557,uu____7558::is) ->
                                             let uu____7600 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____7600
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____7633 ->
                                             let uu____7634 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____7634 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____7650 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____7650)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____7655 =
                                           let uu____7656 =
                                             let uu____7659 =
                                               let uu____7660 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____7660.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____7659
                                              in
                                           uu____7656.FStar_Syntax_Syntax.n
                                            in
                                         match uu____7655 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____7671,uu____7672::is) ->
                                             let uu____7714 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____7714
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____7747 ->
                                             let uu____7748 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____7748 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____7764 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____7764)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____7769 =
                                         let uu____7770 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____7770.FStar_Syntax_Syntax.n  in
                                       match uu____7769 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____7775,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____7830 ->
                                           let uu____7831 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____7831 r
                                        in
                                     let uu____7840 =
                                       let uu____7841 =
                                         let uu____7842 =
                                           FStar_All.pipe_right is
                                             (FStar_List.map
                                                FStar_Syntax_Syntax.as_arg)
                                            in
                                         {
                                           FStar_Syntax_Syntax.comp_univs =
                                             [u_a];
                                           FStar_Syntax_Syntax.effect_name =
                                             (ed.FStar_Syntax_Syntax.mname);
                                           FStar_Syntax_Syntax.result_typ = a;
                                           FStar_Syntax_Syntax.effect_args =
                                             uu____7842;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____7841
                                        in
                                     let uu____7865 =
                                       let uu____7866 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____7866 g_guard
                                        in
                                     (uu____7840, uu____7865))))
  
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
  fun env  ->
    fun ed  ->
      fun u_a  ->
        fun a  ->
          fun p  ->
            fun ct1  ->
              fun ct2  ->
                fun uu____7911  ->
                  let if_then_else1 =
                    let uu____7917 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____7917 FStar_Util.must  in
                  let uu____7924 = destruct_wp_comp ct1  in
                  match uu____7924 with
                  | (uu____7935,uu____7936,wp_t) ->
                      let uu____7938 = destruct_wp_comp ct2  in
                      (match uu____7938 with
                       | (uu____7949,uu____7950,wp_e) ->
                           let wp =
                             let uu____7955 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             let uu____7956 =
                               let uu____7961 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_a] env ed if_then_else1
                                  in
                               let uu____7962 =
                                 let uu____7963 =
                                   FStar_Syntax_Syntax.as_arg a  in
                                 let uu____7972 =
                                   let uu____7983 =
                                     FStar_Syntax_Syntax.as_arg p  in
                                   let uu____7992 =
                                     let uu____8003 =
                                       FStar_Syntax_Syntax.as_arg wp_t  in
                                     let uu____8012 =
                                       let uu____8023 =
                                         FStar_Syntax_Syntax.as_arg wp_e  in
                                       [uu____8023]  in
                                     uu____8003 :: uu____8012  in
                                   uu____7983 :: uu____7992  in
                                 uu____7963 :: uu____7972  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____7961
                                 uu____7962
                                in
                             uu____7956 FStar_Pervasives_Native.None
                               uu____7955
                              in
                           let uu____8072 = mk_comp ed u_a a wp []  in
                           (uu____8072, FStar_TypeChecker_Env.trivial_guard))
  
let (bind_cases :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ * FStar_Ident.lident *
        FStar_Syntax_Syntax.cflag Prims.list *
        (Prims.bool -> FStar_TypeChecker_Common.lcomp)) Prims.list ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun res_t  ->
      fun lcases  ->
        let eff =
          FStar_List.fold_left
            (fun eff  ->
               fun uu____8142  ->
                 match uu____8142 with
                 | (uu____8156,eff_label,uu____8158,uu____8159) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____8172 =
          let uu____8180 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____8218  ->
                    match uu____8218 with
                    | (uu____8233,uu____8234,flags,uu____8236) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_8253  ->
                                match uu___5_8253 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____8256 -> false))))
             in
          if uu____8180
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____8172 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____8293 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____8295 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____8295
              then
                let uu____8302 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                   in
                (uu____8302, FStar_TypeChecker_Env.trivial_guard)
              else
                (let default_case =
                   let post_k =
                     let uu____8309 =
                       let uu____8318 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____8318]  in
                     let uu____8337 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____8309 uu____8337  in
                   let kwp =
                     let uu____8343 =
                       let uu____8352 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____8352]  in
                     let uu____8371 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____8343 uu____8371  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____8378 =
                       let uu____8379 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____8379]  in
                     let uu____8398 =
                       let uu____8401 =
                         let uu____8408 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____8408
                          in
                       let uu____8409 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____8401 uu____8409  in
                     FStar_Syntax_Util.abs uu____8378 uu____8398
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
                   let uu____8433 =
                     should_not_inline_whole_match ||
                       (let uu____8436 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____8436)
                      in
                   if uu____8433 then cthen true else cthen false  in
                 let uu____8443 =
                   FStar_List.fold_right
                     (fun uu____8496  ->
                        fun uu____8497  ->
                          match (uu____8496, uu____8497) with
                          | ((g,eff_label,uu____8551,cthen),(uu____8553,celse,g_comp))
                              ->
                              let uu____8594 =
                                let uu____8599 = maybe_return eff_label cthen
                                   in
                                FStar_TypeChecker_Common.lcomp_comp
                                  uu____8599
                                 in
                              (match uu____8594 with
                               | (cthen1,gthen) ->
                                   let uu____8610 =
                                     let uu____8619 =
                                       lift_comps env cthen1 celse
                                         FStar_Pervasives_Native.None false
                                        in
                                     match uu____8619 with
                                     | (m,cthen2,celse1,g_lift) ->
                                         let md =
                                           FStar_TypeChecker_Env.get_effect_decl
                                             env m
                                            in
                                         let uu____8642 =
                                           FStar_All.pipe_right cthen2
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         let uu____8643 =
                                           FStar_All.pipe_right celse1
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         (md, uu____8642, uu____8643, g_lift)
                                      in
                                   (match uu____8610 with
                                    | (md,ct_then,ct_else,g_lift) ->
                                        let fn =
                                          let uu____8693 =
                                            FStar_All.pipe_right md
                                              FStar_Syntax_Util.is_layered
                                             in
                                          if uu____8693
                                          then mk_layered_conjunction
                                          else mk_non_layered_conjunction  in
                                        let uu____8727 =
                                          let uu____8732 =
                                            FStar_TypeChecker_Env.get_range
                                              env
                                             in
                                          fn env md u_res_t res_t g ct_then
                                            ct_else uu____8732
                                           in
                                        (match uu____8727 with
                                         | (c,g_conjunction) ->
                                             let uu____8743 =
                                               let uu____8744 =
                                                 let uu____8745 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_comp gthen
                                                    in
                                                 FStar_TypeChecker_Env.conj_guard
                                                   uu____8745 g_lift
                                                  in
                                               FStar_TypeChecker_Env.conj_guard
                                                 uu____8744 g_conjunction
                                                in
                                             ((FStar_Pervasives_Native.Some
                                                 md), c, uu____8743)))))
                     lcases
                     (FStar_Pervasives_Native.None, default_case,
                       FStar_TypeChecker_Env.trivial_guard)
                    in
                 match uu____8443 with
                 | (md,comp,g_comp) ->
                     (match lcases with
                      | [] -> (comp, g_comp)
                      | uu____8779::[] -> (comp, g_comp)
                      | uu____8822 ->
                          let uu____8839 =
                            let uu____8841 =
                              FStar_All.pipe_right md FStar_Util.must  in
                            FStar_All.pipe_right uu____8841
                              FStar_Syntax_Util.is_layered
                             in
                          if uu____8839
                          then (comp, g_comp)
                          else
                            (let comp1 =
                               FStar_TypeChecker_Env.comp_to_comp_typ env
                                 comp
                                in
                             let md1 =
                               FStar_TypeChecker_Env.get_effect_decl env
                                 comp1.FStar_Syntax_Syntax.effect_name
                                in
                             let uu____8854 = destruct_wp_comp comp1  in
                             match uu____8854 with
                             | (uu____8865,uu____8866,wp) ->
                                 let ite_wp =
                                   let uu____8869 =
                                     FStar_All.pipe_right md1
                                       FStar_Syntax_Util.get_wp_ite_combinator
                                      in
                                   FStar_All.pipe_right uu____8869
                                     FStar_Util.must
                                    in
                                 let wp1 =
                                   let uu____8879 =
                                     let uu____8884 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_res_t] env md1 ite_wp
                                        in
                                     let uu____8885 =
                                       let uu____8886 =
                                         FStar_Syntax_Syntax.as_arg res_t  in
                                       let uu____8895 =
                                         let uu____8906 =
                                           FStar_Syntax_Syntax.as_arg wp  in
                                         [uu____8906]  in
                                       uu____8886 :: uu____8895  in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____8884
                                       uu____8885
                                      in
                                   uu____8879 FStar_Pervasives_Native.None
                                     wp.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____8939 =
                                   mk_comp md1 u_res_t res_t wp1
                                     bind_cases_flags
                                    in
                                 (uu____8939, g_comp))))
               in
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
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____8973 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____8973 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____8989 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____8995 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____8989 uu____8995
              else
                (let uu____9004 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____9010 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____9004 uu____9010)
          | FStar_Pervasives_Native.Some g -> (e, c', g)
  
let (universe_of_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u_res  ->
      fun c  ->
        let c_lid =
          let uu____9035 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____9035
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____9038 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____9038
        then u_res
        else
          (let is_total =
             let uu____9045 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____9045
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____9056 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____9056 with
              | FStar_Pervasives_Native.None  ->
                  let uu____9059 =
                    let uu____9065 =
                      let uu____9067 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____9067
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____9065)
                     in
                  FStar_Errors.raise_error uu____9059
                    c.FStar_Syntax_Syntax.pos
              | FStar_Pervasives_Native.Some tm ->
                  env.FStar_TypeChecker_Env.universe_of env tm))
  
let (check_trivial_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp_typ * FStar_Syntax_Syntax.formula *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c  ->
      let ct =
        FStar_All.pipe_right c
          (FStar_TypeChecker_Env.unfold_effect_abbrev env)
         in
      let md =
        FStar_TypeChecker_Env.get_effect_decl env
          ct.FStar_Syntax_Syntax.effect_name
         in
      let uu____9091 = destruct_wp_comp ct  in
      match uu____9091 with
      | (u_t,t,wp) ->
          let vc =
            let uu____9110 = FStar_TypeChecker_Env.get_range env  in
            let uu____9111 =
              let uu____9116 =
                let uu____9117 =
                  let uu____9118 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_trivial_combinator
                     in
                  FStar_All.pipe_right uu____9118 FStar_Util.must  in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____9117
                 in
              let uu____9125 =
                let uu____9126 = FStar_Syntax_Syntax.as_arg t  in
                let uu____9135 =
                  let uu____9146 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____9146]  in
                uu____9126 :: uu____9135  in
              FStar_Syntax_Syntax.mk_Tm_app uu____9116 uu____9125  in
            uu____9111 FStar_Pervasives_Native.None uu____9110  in
          let uu____9179 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____9179)
  
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
  fun env  ->
    fun e  ->
      fun lc  ->
        fun ty  ->
          fun f  ->
            fun us  ->
              fun eargs  ->
                fun mkcomp  ->
                  let uu____9234 = FStar_TypeChecker_Env.try_lookup_lid env f
                     in
                  match uu____9234 with
                  | FStar_Pervasives_Native.Some uu____9249 ->
                      ((let uu____9267 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____9267
                        then
                          let uu____9271 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____9271
                        else ());
                       (let coercion =
                          let uu____9277 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____9277
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____9284 =
                            let uu____9285 =
                              let uu____9286 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____9286
                               in
                            (FStar_Pervasives_Native.None, uu____9285)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____9284
                           in
                        let e1 =
                          let uu____9292 =
                            let uu____9297 =
                              let uu____9298 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____9298]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____9297
                             in
                          uu____9292 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____9332 =
                          let uu____9338 =
                            let uu____9340 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____9340
                             in
                          (FStar_Errors.Warning_CoercionNotFound, uu____9338)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____9332);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____9359 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____9377 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____9388 -> false 
let (check_erased :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> isErased) =
  fun env  ->
    fun t  ->
      let norm' =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
          FStar_TypeChecker_Env.Primops;
          FStar_TypeChecker_Env.Weak;
          FStar_TypeChecker_Env.HNF]
         in
      let t1 = norm' env t  in
      let t2 = FStar_Syntax_Util.unrefine t1  in
      let uu____9412 = FStar_Syntax_Util.head_and_args t2  in
      match uu____9412 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____9457 =
              let uu____9472 =
                let uu____9473 = FStar_Syntax_Subst.compress h1  in
                uu____9473.FStar_Syntax_Syntax.n  in
              (uu____9472, args)  in
            match uu____9457 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____9520,uu____9521) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____9554) -> Maybe
            | uu____9575 -> No  in
          r
  
let (maybe_coerce_lc :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun exp_t  ->
          let should_coerce =
            (((let uu____9627 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____9627) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____9646 =
                 let uu____9647 = FStar_Syntax_Subst.compress t1  in
                 uu____9647.FStar_Syntax_Syntax.n  in
               match uu____9646 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____9652 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____9662 =
                 let uu____9663 = FStar_Syntax_Subst.compress t1  in
                 uu____9663.FStar_Syntax_Syntax.n  in
               match uu____9662 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____9668 -> false  in
             let is_type1 t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____9678 =
                 let uu____9679 = FStar_Syntax_Subst.compress t1  in
                 uu____9679.FStar_Syntax_Syntax.n  in
               match uu____9678 with
               | FStar_Syntax_Syntax.Tm_type uu____9683 -> true
               | uu____9685 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____9688 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____9688 with
             | (head1,args) ->
                 ((let uu____9738 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____9738
                   then
                     let uu____9742 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____9744 = FStar_Syntax_Print.term_to_string e  in
                     let uu____9746 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____9748 = FStar_Syntax_Print.term_to_string exp_t
                        in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____9742 uu____9744 uu____9746 uu____9748
                   else ());
                  (let mk_erased u t =
                     let uu____9766 =
                       let uu____9769 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____9769 [u]  in
                     let uu____9770 =
                       let uu____9781 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____9781]  in
                     FStar_Syntax_Util.mk_app uu____9766 uu____9770  in
                   let uu____9806 =
                     let uu____9821 =
                       let uu____9822 = FStar_Syntax_Util.un_uinst head1  in
                       uu____9822.FStar_Syntax_Syntax.n  in
                     (uu____9821, args)  in
                   match uu____9806 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type1 exp_t)
                       ->
                       let uu____9860 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____9860 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____9900 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____9900 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____9940 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____9940 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____9980 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____9980 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____10001 ->
                       let uu____10016 =
                         let uu____10021 = check_erased env res_typ  in
                         let uu____10022 = check_erased env exp_t  in
                         (uu____10021, uu____10022)  in
                       (match uu____10016 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____10031 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____10031 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____10042 =
                                   let uu____10047 =
                                     let uu____10048 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____10048]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____10047
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____10042 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____10083 =
                              let uu____10088 =
                                let uu____10089 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____10089]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____10088
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____10083 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____10122 ->
                            (e, lc, FStar_TypeChecker_Env.trivial_guard)))))
  
let (coerce_views :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let rt = lc.FStar_TypeChecker_Common.res_typ  in
        let rt1 = FStar_Syntax_Util.unrefine rt  in
        let uu____10157 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____10157 with
        | (hd1,args) ->
            let uu____10206 =
              let uu____10221 =
                let uu____10222 = FStar_Syntax_Subst.compress hd1  in
                uu____10222.FStar_Syntax_Syntax.n  in
              (uu____10221, args)  in
            (match uu____10206 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____10260 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun _10287  -> FStar_Pervasives_Native.Some _10287)
                   uu____10260
             | uu____10288 -> FStar_Pervasives_Native.None)
  
let (weaken_result_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          (let uu____10341 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____10341
           then
             let uu____10344 = FStar_Syntax_Print.term_to_string e  in
             let uu____10346 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____10348 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____10344 uu____10346 uu____10348
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____10358 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____10358 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____10383 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____10409 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____10409, false)
             else
               (let uu____10419 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____10419, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____10432) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____10444 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____10444
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1232_10460 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1232_10460.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1232_10460.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1232_10460.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____10467 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____10467 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____10483 =
                      let uu____10484 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____10484 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____10504 =
                            let uu____10506 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____10506 = FStar_Syntax_Util.Equal  in
                          if uu____10504
                          then
                            ((let uu____10513 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____10513
                              then
                                let uu____10517 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____10519 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____10517 uu____10519
                              else ());
                             (let uu____10524 = set_result_typ1 c  in
                              (uu____10524, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____10531 ->
                                   true
                               | uu____10539 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____10548 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____10548
                                  in
                               let lc1 =
                                 let uu____10550 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____10551 =
                                   let uu____10552 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____10552)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____10550 uu____10551
                                  in
                               ((let uu____10556 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____10556
                                 then
                                   let uu____10560 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____10562 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____10564 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____10566 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____10560 uu____10562 uu____10564
                                     uu____10566
                                 else ());
                                (let uu____10571 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____10571 with
                                 | (c1,g_lc) ->
                                     let uu____10582 = set_result_typ1 c1  in
                                     let uu____10583 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____10582, uu____10583)))
                             else
                               ((let uu____10587 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____10587
                                 then
                                   let uu____10591 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____10593 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____10591 uu____10593
                                 else ());
                                (let uu____10598 = set_result_typ1 c  in
                                 (uu____10598, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1269_10602 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1269_10602.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1269_10602.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1269_10602.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____10612 =
                      let uu____10613 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____10613
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____10623 =
                           let uu____10624 = FStar_Syntax_Subst.compress f1
                              in
                           uu____10624.FStar_Syntax_Syntax.n  in
                         match uu____10623 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____10631,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____10633;
                                            FStar_Syntax_Syntax.vars =
                                              uu____10634;_},uu____10635)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1285_10661 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1285_10661.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1285_10661.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1285_10661.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____10662 ->
                             let uu____10663 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____10663 with
                              | (c,g_c) ->
                                  ((let uu____10675 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____10675
                                    then
                                      let uu____10679 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____10681 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____10683 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____10685 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____10679 uu____10681 uu____10683
                                        uu____10685
                                    else ());
                                   (let u_t_opt = comp_univ_opt c  in
                                    let x =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (t.FStar_Syntax_Syntax.pos)) t
                                       in
                                    let xexp =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    let cret =
                                      return_value env u_t_opt t xexp  in
                                    let guard =
                                      if apply_guard1
                                      then
                                        let uu____10698 =
                                          let uu____10703 =
                                            let uu____10704 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____10704]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____10703
                                           in
                                        uu____10698
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____10731 =
                                      let uu____10736 =
                                        FStar_All.pipe_left
                                          (fun _10757  ->
                                             FStar_Pervasives_Native.Some
                                               _10757)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____10758 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____10759 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____10760 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____10736
                                        uu____10758 e uu____10759 uu____10760
                                       in
                                    match uu____10731 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1303_10768 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1303_10768.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1303_10768.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____10770 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____10770
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____10773 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____10773 with
                                         | (c2,g_lc) ->
                                             ((let uu____10785 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____10785
                                               then
                                                 let uu____10789 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____10789
                                               else ());
                                              (let uu____10794 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____10794))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_10803  ->
                              match uu___6_10803 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____10806 -> []))
                       in
                    let lc1 =
                      let uu____10808 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____10808 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1319_10810 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1319_10810.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1319_10810.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1319_10810.FStar_TypeChecker_Common.implicits)
                      }  in
                    (e, lc1, g2)))
  
let (pure_or_ghost_pre_and_post :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option *
        FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun comp  ->
      let mk_post_type res_t ens =
        let x = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t
           in
        let uu____10846 =
          let uu____10849 =
            let uu____10854 =
              let uu____10855 =
                let uu____10864 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____10864  in
              [uu____10855]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____10854  in
          uu____10849 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____10846  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____10887 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____10887
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____10906 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____10922 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____10939 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____10939
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____10955)::(ens,uu____10957)::uu____10958 ->
                    let uu____11001 =
                      let uu____11004 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____11004  in
                    let uu____11005 =
                      let uu____11006 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____11006  in
                    (uu____11001, uu____11005)
                | uu____11009 ->
                    let uu____11020 =
                      let uu____11026 =
                        let uu____11028 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____11028
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____11026)
                       in
                    FStar_Errors.raise_error uu____11020
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____11048)::uu____11049 ->
                    let uu____11076 =
                      let uu____11081 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____11081
                       in
                    (match uu____11076 with
                     | (us_r,uu____11113) ->
                         let uu____11114 =
                           let uu____11119 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____11119
                            in
                         (match uu____11114 with
                          | (us_e,uu____11151) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____11154 =
                                  let uu____11155 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____11155
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____11154
                                  us_r
                                 in
                              let as_ens =
                                let uu____11157 =
                                  let uu____11158 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____11158
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____11157
                                  us_e
                                 in
                              let req =
                                let uu____11162 =
                                  let uu____11167 =
                                    let uu____11168 =
                                      let uu____11179 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____11179]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____11168
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____11167
                                   in
                                uu____11162 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____11219 =
                                  let uu____11224 =
                                    let uu____11225 =
                                      let uu____11236 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____11236]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____11225
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____11224
                                   in
                                uu____11219 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____11273 =
                                let uu____11276 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____11276  in
                              let uu____11277 =
                                let uu____11278 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____11278  in
                              (uu____11273, uu____11277)))
                | uu____11281 -> failwith "Impossible"))
  
let (reify_body :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun steps  ->
      fun t  ->
        let tm = FStar_Syntax_Util.mk_reify t  in
        let tm' =
          FStar_TypeChecker_Normalize.normalize
            (FStar_List.append
               [FStar_TypeChecker_Env.Beta;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.Eager_unfolding;
               FStar_TypeChecker_Env.EraseUniverses;
               FStar_TypeChecker_Env.AllowUnboundUniverses;
               FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta]
               steps) env tm
           in
        (let uu____11320 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____11320
         then
           let uu____11325 = FStar_Syntax_Print.term_to_string tm  in
           let uu____11327 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____11325
             uu____11327
         else ());
        tm'
  
let (reify_body_with_arg :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.arg -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun steps  ->
      fun head1  ->
        fun arg  ->
          let tm =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_app (head1, [arg]))
              FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos
             in
          let tm' =
            FStar_TypeChecker_Normalize.normalize
              (FStar_List.append
                 [FStar_TypeChecker_Env.Beta;
                 FStar_TypeChecker_Env.Reify;
                 FStar_TypeChecker_Env.Eager_unfolding;
                 FStar_TypeChecker_Env.EraseUniverses;
                 FStar_TypeChecker_Env.AllowUnboundUniverses;
                 FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta]
                 steps) env tm
             in
          (let uu____11386 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____11386
           then
             let uu____11391 = FStar_Syntax_Print.term_to_string tm  in
             let uu____11393 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____11391
               uu____11393
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____11404 =
      let uu____11406 =
        let uu____11407 = FStar_Syntax_Subst.compress t  in
        uu____11407.FStar_Syntax_Syntax.n  in
      match uu____11406 with
      | FStar_Syntax_Syntax.Tm_app uu____11411 -> false
      | uu____11429 -> true  in
    if uu____11404
    then t
    else
      (let uu____11434 = FStar_Syntax_Util.head_and_args t  in
       match uu____11434 with
       | (head1,args) ->
           let uu____11477 =
             let uu____11479 =
               let uu____11480 = FStar_Syntax_Subst.compress head1  in
               uu____11480.FStar_Syntax_Syntax.n  in
             match uu____11479 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____11485 -> false  in
           if uu____11477
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____11517 ->
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
  fun env  ->
    fun e  ->
      fun t  ->
        let torig = FStar_Syntax_Subst.compress t  in
        if Prims.op_Negation env.FStar_TypeChecker_Env.instantiate_imp
        then (e, torig, FStar_TypeChecker_Env.trivial_guard)
        else
          ((let uu____11564 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____11564
            then
              let uu____11567 = FStar_Syntax_Print.term_to_string e  in
              let uu____11569 = FStar_Syntax_Print.term_to_string t  in
              let uu____11571 =
                let uu____11573 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____11573
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____11567 uu____11569 uu____11571
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____11586 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____11586 with
              | (formals,uu____11602) ->
                  let n_implicits =
                    let uu____11624 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____11702  ->
                              match uu____11702 with
                              | (uu____11710,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____11717 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____11717 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____11624 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____11842 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____11842 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____11856 =
                      let uu____11862 =
                        let uu____11864 = FStar_Util.string_of_int n_expected
                           in
                        let uu____11866 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____11868 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____11864 uu____11866 uu____11868
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____11862)
                       in
                    let uu____11872 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____11856 uu____11872
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_11890 =
              match uu___7_11890 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____11933 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____11933 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _12064,uu____12051)
                           when _12064 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____12097,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____12099))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____12133 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____12133 with
                            | (v1,uu____12174,g) ->
                                ((let uu____12189 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____12189
                                  then
                                    let uu____12192 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____12192
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____12202 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____12202 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____12295 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____12295))))
                       | (uu____12322,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____12359 =
                             let uu____12372 =
                               let uu____12379 =
                                 let uu____12384 = FStar_Dyn.mkdyn env  in
                                 (uu____12384, tau)  in
                               FStar_Pervasives_Native.Some uu____12379  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____12372
                              in
                           (match uu____12359 with
                            | (v1,uu____12417,g) ->
                                ((let uu____12432 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____12432
                                  then
                                    let uu____12435 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____12435
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____12445 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____12445 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____12538 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____12538))))
                       | (uu____12565,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____12613 =
                       let uu____12640 = inst_n_binders t1  in
                       aux [] uu____12640 bs1  in
                     (match uu____12613 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____12712) -> (e, torig, guard)
                           | (uu____12743,[]) when
                               let uu____12774 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____12774 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____12776 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____12804 ->
                                     FStar_Syntax_Util.arrow bs2 c1
                                  in
                               let t3 = FStar_Syntax_Subst.subst subst1 t2
                                  in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   FStar_Pervasives_Native.None
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               (e1, t3, guard))))
            | uu____12817 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____12829 =
      let uu____12833 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____12833
        (FStar_List.map
           (fun u  ->
              let uu____12845 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____12845 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____12829 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____12873 = FStar_Util.set_is_empty x  in
      if uu____12873
      then []
      else
        (let s =
           let uu____12891 =
             let uu____12894 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____12894  in
           FStar_All.pipe_right uu____12891 FStar_Util.set_elements  in
         (let uu____12910 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____12910
          then
            let uu____12915 =
              let uu____12917 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____12917  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____12915
          else ());
         (let r =
            let uu____12926 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____12926  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____12965 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____12965
                     then
                       let uu____12970 =
                         let uu____12972 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____12972
                          in
                       let uu____12976 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____12978 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____12970 uu____12976 uu____12978
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
        let uu____13008 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____13008 FStar_Util.set_elements  in
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
        | ([],uu____13047) -> generalized_univ_names
        | (uu____13054,[]) -> explicit_univ_names
        | uu____13061 ->
            let uu____13070 =
              let uu____13076 =
                let uu____13078 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____13078
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____13076)
               in
            FStar_Errors.raise_error uu____13070 t.FStar_Syntax_Syntax.pos
  
let (generalize_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.NoFullNorm;
          FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.DoNotUnfoldPureLets] env t0
         in
      let univnames1 = gather_free_univnames env t  in
      (let uu____13100 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____13100
       then
         let uu____13105 = FStar_Syntax_Print.term_to_string t  in
         let uu____13107 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____13105 uu____13107
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____13116 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____13116
        then
          let uu____13121 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____13121
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____13130 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____13130
         then
           let uu____13135 = FStar_Syntax_Print.term_to_string t  in
           let uu____13137 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____13135 uu____13137
         else ());
        (let univs2 = check_universe_generalization univnames1 gen1 t0  in
         let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t  in
         let ts = FStar_Syntax_Subst.close_univ_vars univs2 t1  in
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
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        let uu____13221 =
          let uu____13223 =
            FStar_Util.for_all
              (fun uu____13237  ->
                 match uu____13237 with
                 | (uu____13247,uu____13248,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____13223  in
        if uu____13221
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____13300 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____13300
              then
                let uu____13303 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____13303
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____13310 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____13310
               then
                 let uu____13313 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____13313
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____13331 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____13331 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____13365 =
             match uu____13365 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____13402 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____13402
                   then
                     let uu____13407 =
                       let uu____13409 =
                         let uu____13413 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____13413
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____13409
                         (FStar_String.concat ", ")
                        in
                     let uu____13461 =
                       let uu____13463 =
                         let uu____13467 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____13467
                           (FStar_List.map
                              (fun u  ->
                                 let uu____13480 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____13482 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____13480
                                   uu____13482))
                          in
                       FStar_All.pipe_right uu____13463
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____13407
                       uu____13461
                   else ());
                  (let univs2 =
                     let uu____13496 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____13508 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____13508) univs1
                       uu____13496
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____13515 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____13515
                    then
                      let uu____13520 =
                        let uu____13522 =
                          let uu____13526 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____13526
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____13522
                          (FStar_String.concat ", ")
                         in
                      let uu____13574 =
                        let uu____13576 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____13590 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____13592 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____13590
                                    uu____13592))
                           in
                        FStar_All.pipe_right uu____13576
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____13520 uu____13574
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____13613 =
             let uu____13630 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____13630  in
           match uu____13613 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____13720 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____13720
                 then ()
                 else
                   (let uu____13725 = lec_hd  in
                    match uu____13725 with
                    | (lb1,uu____13733,uu____13734) ->
                        let uu____13735 = lec2  in
                        (match uu____13735 with
                         | (lb2,uu____13743,uu____13744) ->
                             let msg =
                               let uu____13747 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____13749 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____13747 uu____13749
                                in
                             let uu____13752 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____13752))
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
                 let uu____13820 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____13820
                 then ()
                 else
                   (let uu____13825 = lec_hd  in
                    match uu____13825 with
                    | (lb1,uu____13833,uu____13834) ->
                        let uu____13835 = lec2  in
                        (match uu____13835 with
                         | (lb2,uu____13843,uu____13844) ->
                             let msg =
                               let uu____13847 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____13849 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____13847 uu____13849
                                in
                             let uu____13852 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____13852))
                  in
               let lecs1 =
                 let uu____13863 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____13916 = univs_and_uvars_of_lec this_lec  in
                        match uu____13916 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____13863 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____14021 = lec_hd  in
                   match uu____14021 with
                   | (lbname,e,c) ->
                       let uu____14031 =
                         let uu____14037 =
                           let uu____14039 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____14041 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____14043 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____14039 uu____14041 uu____14043
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____14037)
                          in
                       let uu____14047 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____14031 uu____14047
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____14066 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____14066 with
                         | FStar_Pervasives_Native.Some uu____14075 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____14083 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____14087 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____14087 with
                              | (bs,kres) ->
                                  ((let uu____14131 =
                                      let uu____14132 =
                                        let uu____14135 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____14135
                                         in
                                      uu____14132.FStar_Syntax_Syntax.n  in
                                    match uu____14131 with
                                    | FStar_Syntax_Syntax.Tm_type uu____14136
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____14140 =
                                          let uu____14142 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____14142  in
                                        if uu____14140
                                        then fail1 kres
                                        else ()
                                    | uu____14147 -> fail1 kres);
                                   (let a =
                                      let uu____14149 =
                                        let uu____14152 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _14155  ->
                                             FStar_Pervasives_Native.Some
                                               _14155) uu____14152
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____14149
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____14163 ->
                                          let uu____14172 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____14172
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
                      (fun uu____14275  ->
                         match uu____14275 with
                         | (lbname,e,c) ->
                             let uu____14321 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____14382 ->
                                   let uu____14395 = (e, c)  in
                                   (match uu____14395 with
                                    | (e0,c0) ->
                                        let c1 =
                                          FStar_TypeChecker_Normalize.normalize_comp
                                            [FStar_TypeChecker_Env.Beta;
                                            FStar_TypeChecker_Env.DoNotUnfoldPureLets;
                                            FStar_TypeChecker_Env.CompressUvars;
                                            FStar_TypeChecker_Env.NoFullNorm;
                                            FStar_TypeChecker_Env.Exclude
                                              FStar_TypeChecker_Env.Zeta] env
                                            c
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
                                                (fun uu____14435  ->
                                                   match uu____14435 with
                                                   | (x,uu____14441) ->
                                                       let uu____14442 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____14442)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____14460 =
                                                let uu____14462 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____14462
                                                 in
                                              if uu____14460
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
                                          let uu____14471 =
                                            let uu____14472 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____14472.FStar_Syntax_Syntax.n
                                             in
                                          match uu____14471 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____14497 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____14497 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____14508 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____14512 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____14512, gen_tvars))
                                in
                             (match uu____14321 with
                              | (e1,c1,gvs) ->
                                  (lbname, gen_univs1, e1, c1, gvs))))
                  in
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
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        (let uu____14659 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____14659
         then
           let uu____14662 =
             let uu____14664 =
               FStar_List.map
                 (fun uu____14679  ->
                    match uu____14679 with
                    | (lb,uu____14688,uu____14689) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____14664 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____14662
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____14715  ->
                match uu____14715 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____14744 = gen env is_rec lecs  in
           match uu____14744 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____14843  ->
                       match uu____14843 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____14905 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____14905
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____14953  ->
                           match uu____14953 with
                           | (l,us,e,c,gvs) ->
                               let uu____14987 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____14989 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____14991 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____14993 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____14995 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____14987 uu____14989 uu____14991
                                 uu____14993 uu____14995))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____15040  ->
                match uu____15040 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____15084 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____15084, t, c, gvs)) univnames_lecs
           generalized_lecs)
  
let (check_and_ascribe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t2  ->
          let env1 =
            FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
          let check1 env2 t1 t21 =
            if env2.FStar_TypeChecker_Env.use_eq
            then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
            else
              (let uu____15149 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                  in
               match uu____15149 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____15155 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _15158  -> FStar_Pervasives_Native.Some _15158)
                     uu____15155)
             in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1772_15178 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1772_15178.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1772_15178.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____15179 -> e2  in
          let uu____15180 = maybe_coerce_lc env1 e lc t2  in
          match uu____15180 with
          | (e1,lc1,g_c) ->
              let uu____15196 =
                check1 env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____15196 with
               | FStar_Pervasives_Native.None  ->
                   let uu____15205 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____15211 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____15205 uu____15211
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____15220 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____15220
                     then
                       let uu____15225 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____15225
                     else ());
                    (let uu____15231 = decorate e1 t2  in
                     let uu____15232 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (uu____15231, lc1, uu____15232))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____15260 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____15260
         then
           let uu____15263 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____15263
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____15277 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____15277 with
         | (c,g_c) ->
             let uu____15289 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____15289
             then
               let uu____15297 =
                 let uu____15299 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____15299  in
               (uu____15297, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____15307 =
                    let uu____15308 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____15308
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____15307
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____15309 = check_trivial_precondition env c1  in
                match uu____15309 with
                | (ct,vc,g_pre) ->
                    ((let uu____15325 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____15325
                      then
                        let uu____15330 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____15330
                      else ());
                     (let uu____15335 =
                        let uu____15337 =
                          let uu____15338 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____15338  in
                        discharge uu____15337  in
                      let uu____15339 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____15335, uu____15339)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_15373 =
        match uu___8_15373 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____15383)::[] -> f fst1
        | uu____15408 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____15420 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____15420
          (fun _15421  -> FStar_TypeChecker_Common.NonTrivial _15421)
         in
      let op_or_e e =
        let uu____15432 =
          let uu____15433 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____15433  in
        FStar_All.pipe_right uu____15432
          (fun _15436  -> FStar_TypeChecker_Common.NonTrivial _15436)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _15443  -> FStar_TypeChecker_Common.NonTrivial _15443)
         in
      let op_or_t t =
        let uu____15454 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____15454
          (fun _15457  -> FStar_TypeChecker_Common.NonTrivial _15457)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _15464  -> FStar_TypeChecker_Common.NonTrivial _15464)
         in
      let short_op_ite uu___9_15470 =
        match uu___9_15470 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____15480)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____15507)::[] ->
            let uu____15548 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____15548
              (fun _15549  -> FStar_TypeChecker_Common.NonTrivial _15549)
        | uu____15550 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____15562 =
          let uu____15570 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____15570)  in
        let uu____15578 =
          let uu____15588 =
            let uu____15596 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____15596)  in
          let uu____15604 =
            let uu____15614 =
              let uu____15622 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____15622)  in
            let uu____15630 =
              let uu____15640 =
                let uu____15648 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____15648)  in
              let uu____15656 =
                let uu____15666 =
                  let uu____15674 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____15674)  in
                [uu____15666; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____15640 :: uu____15656  in
            uu____15614 :: uu____15630  in
          uu____15588 :: uu____15604  in
        uu____15562 :: uu____15578  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____15736 =
            FStar_Util.find_map table
              (fun uu____15751  ->
                 match uu____15751 with
                 | (x,mk1) ->
                     let uu____15768 = FStar_Ident.lid_equals x lid  in
                     if uu____15768
                     then
                       let uu____15773 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____15773
                     else FStar_Pervasives_Native.None)
             in
          (match uu____15736 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____15777 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____15785 =
      let uu____15786 = FStar_Syntax_Util.un_uinst l  in
      uu____15786.FStar_Syntax_Syntax.n  in
    match uu____15785 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____15791 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____15827)::uu____15828 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____15847 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____15856,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____15857))::uu____15858 -> bs
      | uu____15876 ->
          let uu____15877 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____15877 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____15881 =
                 let uu____15882 = FStar_Syntax_Subst.compress t  in
                 uu____15882.FStar_Syntax_Syntax.n  in
               (match uu____15881 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____15886) ->
                    let uu____15907 =
                      FStar_Util.prefix_until
                        (fun uu___10_15947  ->
                           match uu___10_15947 with
                           | (uu____15955,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____15956)) ->
                               false
                           | uu____15961 -> true) bs'
                       in
                    (match uu____15907 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____15997,uu____15998) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____16070,uu____16071) ->
                         let uu____16144 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____16164  ->
                                   match uu____16164 with
                                   | (x,uu____16173) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____16144
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____16222  ->
                                     match uu____16222 with
                                     | (x,i) ->
                                         let uu____16241 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____16241, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____16252 -> bs))
  
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
            let uu____16281 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____16281
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
          let uu____16312 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____16312
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
        (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun lident  ->
      fun def  ->
        (let uu____16355 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____16355
         then
           ((let uu____16360 = FStar_Ident.text_of_lid lident  in
             d uu____16360);
            (let uu____16362 = FStar_Ident.text_of_lid lident  in
             let uu____16364 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____16362 uu____16364))
         else ());
        (let fv =
           let uu____16370 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____16370
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
         let uu____16382 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1933_16384 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1933_16384.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1933_16384.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1933_16384.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1933_16384.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___1933_16384.FStar_Syntax_Syntax.sigopts)
           }), uu____16382))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_16402 =
        match uu___11_16402 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____16405 -> false  in
      let reducibility uu___12_16413 =
        match uu___12_16413 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____16420 -> false  in
      let assumption uu___13_16428 =
        match uu___13_16428 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____16432 -> false  in
      let reification uu___14_16440 =
        match uu___14_16440 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____16443 -> true
        | uu____16445 -> false  in
      let inferred uu___15_16453 =
        match uu___15_16453 with
        | FStar_Syntax_Syntax.Discriminator uu____16455 -> true
        | FStar_Syntax_Syntax.Projector uu____16457 -> true
        | FStar_Syntax_Syntax.RecordType uu____16463 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____16473 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____16486 -> false  in
      let has_eq uu___16_16494 =
        match uu___16_16494 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____16498 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____16577 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____16584 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____16617 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____16617))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____16648 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____16648
                       FStar_Parser_Const.erasable_attr)))
           in
        let se_has_erasable_attr =
          FStar_Syntax_Util.has_attribute se1.FStar_Syntax_Syntax.sigattrs
            FStar_Parser_Const.erasable_attr
           in
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
           | FStar_Syntax_Syntax.Sig_bundle uu____16668 ->
               let uu____16677 =
                 let uu____16679 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_16685  ->
                           match uu___17_16685 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____16688 -> false))
                    in
                 Prims.op_Negation uu____16679  in
               if uu____16677
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____16695 -> ()
           | uu____16702 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_QulifierListNotPermitted,
                   "Illegal attribute: the `erasable` attribute is only permitted on inductive type definitions")
                 r)
        else ()  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____16716 =
        let uu____16718 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_16724  ->
                  match uu___18_16724 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____16727 -> false))
           in
        FStar_All.pipe_right uu____16718 Prims.op_Negation  in
      if uu____16716
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____16748 =
            let uu____16754 =
              let uu____16756 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____16756 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____16754)  in
          FStar_Errors.raise_error uu____16748 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____16774 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____16782 =
            let uu____16784 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____16784  in
          if uu____16782 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____16795),uu____16796) ->
              ((let uu____16808 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____16808
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____16817 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____16817
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____16828 ->
              ((let uu____16838 =
                  let uu____16840 =
                    FStar_All.pipe_right quals
                      (FStar_Util.for_all
                         (fun x  ->
                            (((((x = FStar_Syntax_Syntax.Abstract) ||
                                  (x =
                                     FStar_Syntax_Syntax.Inline_for_extraction))
                                 || (x = FStar_Syntax_Syntax.NoExtract))
                                || (inferred x))
                               || (visibility x))
                              || (has_eq x)))
                     in
                  Prims.op_Negation uu____16840  in
                if uu____16838 then err'1 () else ());
               (let uu____16850 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_16856  ->
                           match uu___19_16856 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____16859 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____16850
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____16865 ->
              let uu____16872 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____16872 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____16880 ->
              let uu____16887 =
                let uu____16889 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____16889  in
              if uu____16887 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____16899 ->
              let uu____16900 =
                let uu____16902 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____16902  in
              if uu____16900 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____16912 ->
              let uu____16925 =
                let uu____16927 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____16927  in
              if uu____16925 then err'1 () else ()
          | uu____16937 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____16976 =
          let uu____16977 = FStar_Syntax_Subst.compress t1  in
          uu____16977.FStar_Syntax_Syntax.n  in
        match uu____16976 with
        | FStar_Syntax_Syntax.Tm_arrow uu____16981 ->
            let uu____16996 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____16996 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____17029;
               FStar_Syntax_Syntax.index = uu____17030;
               FStar_Syntax_Syntax.sort = t2;_},uu____17032)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____17041) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____17067) ->
            descend env head1
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____17073 -> false
      
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
            FStar_TypeChecker_Env.Unascribe] env t1
           in
        let res =
          (FStar_TypeChecker_Env.non_informative env t2) || (descend env t2)
           in
        (let uu____17083 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____17083
         then
           let uu____17088 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____17088
         else ());
        res
       in aux g t
  
let (fresh_effect_repr :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option ->
            FStar_Syntax_Syntax.universe ->
              FStar_Syntax_Syntax.term ->
                (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun r  ->
      fun eff_name  ->
        fun signature  ->
          fun repr_ts_opt  ->
            fun u  ->
              fun a_tm  ->
                let fail1 t =
                  let uu____17153 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____17153 r  in
                let uu____17163 =
                  let uu____17164 = FStar_Syntax_Subst.compress signature  in
                  uu____17164.FStar_Syntax_Syntax.n  in
                match uu____17163 with
                | FStar_Syntax_Syntax.Tm_arrow (bs,uu____17172) ->
                    let bs1 = FStar_Syntax_Subst.open_binders bs  in
                    (match bs1 with
                     | a::bs2 ->
                         let uu____17220 =
                           FStar_TypeChecker_Env.uvars_for_binders env bs2
                             [FStar_Syntax_Syntax.NT
                                ((FStar_Pervasives_Native.fst a), a_tm)]
                             (fun b  ->
                                let uu____17235 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____17237 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format3
                                  "uvar for binder %s when creating a fresh repr for %s at %s"
                                  uu____17235 eff_name.FStar_Ident.str
                                  uu____17237) r
                            in
                         (match uu____17220 with
                          | (is,g) ->
                              let uu____17250 =
                                match repr_ts_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let eff_c =
                                      let uu____17252 =
                                        let uu____17253 =
                                          FStar_List.map
                                            FStar_Syntax_Syntax.as_arg is
                                           in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            [u];
                                          FStar_Syntax_Syntax.effect_name =
                                            eff_name;
                                          FStar_Syntax_Syntax.result_typ =
                                            a_tm;
                                          FStar_Syntax_Syntax.effect_args =
                                            uu____17253;
                                          FStar_Syntax_Syntax.flags = []
                                        }  in
                                      FStar_Syntax_Syntax.mk_Comp uu____17252
                                       in
                                    let uu____17272 =
                                      let uu____17279 =
                                        let uu____17280 =
                                          let uu____17295 =
                                            let uu____17304 =
                                              FStar_Syntax_Syntax.null_binder
                                                FStar_Syntax_Syntax.t_unit
                                               in
                                            [uu____17304]  in
                                          (uu____17295, eff_c)  in
                                        FStar_Syntax_Syntax.Tm_arrow
                                          uu____17280
                                         in
                                      FStar_Syntax_Syntax.mk uu____17279  in
                                    uu____17272 FStar_Pervasives_Native.None
                                      r
                                | FStar_Pervasives_Native.Some repr_ts ->
                                    let repr =
                                      let uu____17335 =
                                        FStar_TypeChecker_Env.inst_tscheme_with
                                          repr_ts [u]
                                         in
                                      FStar_All.pipe_right uu____17335
                                        FStar_Pervasives_Native.snd
                                       in
                                    let uu____17344 =
                                      let uu____17349 =
                                        FStar_List.map
                                          FStar_Syntax_Syntax.as_arg (a_tm ::
                                          is)
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app repr
                                        uu____17349
                                       in
                                    uu____17344 FStar_Pervasives_Native.None
                                      r
                                 in
                              (uu____17250, g))
                     | uu____17358 -> fail1 signature)
                | uu____17359 -> fail1 signature
  
let (fresh_effect_repr_en :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.universe ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun r  ->
      fun eff_name  ->
        fun u  ->
          fun a_tm  ->
            let signature =
              let uu____17391 =
                let uu____17396 =
                  FStar_TypeChecker_Env.try_lookup_and_inst_lid env [u]
                    eff_name
                   in
                FStar_All.pipe_right uu____17396 FStar_Util.must  in
              FStar_All.pipe_right uu____17391 FStar_Pervasives_Native.fst
               in
            let repr_ts_opt =
              let uu____17424 =
                FStar_TypeChecker_Env.effect_decl_opt env eff_name  in
              FStar_Util.bind_opt uu____17424
                (fun x  ->
                   let uu____17448 =
                     FStar_All.pipe_right x FStar_Pervasives_Native.fst  in
                   FStar_All.pipe_right uu____17448
                     (fun ed  -> FStar_Syntax_Util.get_eff_repr ed))
               in
            fresh_effect_repr env r eff_name signature repr_ts_opt u a_tm
  
let (layered_effect_indices_as_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.tscheme ->
          FStar_Syntax_Syntax.universe ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun r  ->
      fun eff_name  ->
        fun sig_ts  ->
          fun u  ->
            fun a_tm  ->
              let uu____17492 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____17492 with
              | (uu____17497,sig_tm) ->
                  let fail1 t =
                    let uu____17505 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____17505 r  in
                  let uu____17511 =
                    let uu____17512 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____17512.FStar_Syntax_Syntax.n  in
                  (match uu____17511 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____17516) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____17539)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____17561 -> fail1 sig_tm)
                   | uu____17562 -> fail1 sig_tm)
  
let (lift_tf_layered_effect :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun tgt  ->
    fun lift_ts  ->
      fun env  ->
        fun c  ->
          (let uu____17593 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____17593
           then
             let uu____17598 = FStar_Syntax_Print.comp_to_string c  in
             let uu____17600 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____17598 uu____17600
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let effect_args_from_repr repr is_layered1 =
             let err uu____17630 =
               let uu____17631 =
                 let uu____17637 =
                   let uu____17639 = FStar_Syntax_Print.term_to_string repr
                      in
                   let uu____17641 = FStar_Util.string_of_bool is_layered1
                      in
                   FStar_Util.format2
                     "Could not get effect args from repr %s with is_layered %s"
                     uu____17639 uu____17641
                    in
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____17637)  in
               FStar_Errors.raise_error uu____17631 r  in
             let repr1 = FStar_Syntax_Subst.compress repr  in
             if is_layered1
             then
               match repr1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_app (uu____17653,uu____17654::is) ->
                   FStar_All.pipe_right is
                     (FStar_List.map FStar_Pervasives_Native.fst)
               | uu____17722 -> err ()
             else
               (match repr1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (uu____17727,c1) ->
                    let uu____17749 =
                      FStar_All.pipe_right c1
                        FStar_Syntax_Util.comp_to_comp_typ
                       in
                    FStar_All.pipe_right uu____17749
                      (fun ct  ->
                         FStar_All.pipe_right
                           ct.FStar_Syntax_Syntax.effect_args
                           (FStar_List.map FStar_Pervasives_Native.fst))
                | uu____17784 -> err ())
              in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____17786 =
             let uu____17797 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____17798 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____17797, (ct.FStar_Syntax_Syntax.result_typ), uu____17798)
              in
           match uu____17786 with
           | (u,a,c_is) ->
               let uu____17846 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____17846 with
                | (uu____17855,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____17866 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____17868 = FStar_Ident.string_of_lid tgt  in
                      let uu____17870 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____17866 uu____17868 s uu____17870
                       in
                    let uu____17873 =
                      let uu____17906 =
                        let uu____17907 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____17907.FStar_Syntax_Syntax.n  in
                      match uu____17906 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____17971 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____17971 with
                           | (a_b::bs1,c2) ->
                               let uu____18031 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               let uu____18093 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____18031, uu____18093))
                      | uu____18120 ->
                          let uu____18121 =
                            let uu____18127 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____18127)
                             in
                          FStar_Errors.raise_error uu____18121 r
                       in
                    (match uu____17873 with
                     | (a_b,(rest_bs,f_b::[]),lift_ct) ->
                         let uu____18245 =
                           let uu____18252 =
                             let uu____18253 =
                               let uu____18254 =
                                 let uu____18261 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____18261, a)  in
                               FStar_Syntax_Syntax.NT uu____18254  in
                             [uu____18253]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____18252
                             (fun b  ->
                                let uu____18278 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____18280 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____18282 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____18284 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____18278 uu____18280 uu____18282
                                  uu____18284) r
                            in
                         (match uu____18245 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____18298 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____18298
                                then
                                  let uu____18303 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____18312 =
                                             let uu____18314 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____18314
                                              in
                                           Prims.op_Hat s uu____18312) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____18303
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____18345 =
                                           let uu____18352 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____18352, t)  in
                                         FStar_Syntax_Syntax.NT uu____18345)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____18371 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____18371
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____18377 =
                                      let uu____18379 =
                                        FStar_TypeChecker_Env.norm_eff_name
                                          env
                                          ct.FStar_Syntax_Syntax.effect_name
                                         in
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env uu____18379
                                       in
                                    effect_args_from_repr f_sort uu____18377
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____18387 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____18387)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let is =
                                  let uu____18391 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____18391
                                   in
                                let c1 =
                                  let uu____18394 =
                                    let uu____18395 =
                                      let uu____18406 =
                                        FStar_All.pipe_right is
                                          (FStar_List.map
                                             (FStar_Syntax_Subst.subst substs))
                                         in
                                      FStar_All.pipe_right uu____18406
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.as_arg)
                                       in
                                    {
                                      FStar_Syntax_Syntax.comp_univs =
                                        (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                      FStar_Syntax_Syntax.effect_name = tgt;
                                      FStar_Syntax_Syntax.result_typ = a;
                                      FStar_Syntax_Syntax.effect_args =
                                        uu____18395;
                                      FStar_Syntax_Syntax.flags =
                                        (ct.FStar_Syntax_Syntax.flags)
                                    }  in
                                  FStar_Syntax_Syntax.mk_Comp uu____18394  in
                                (let uu____18426 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "LayeredEffects")
                                    in
                                 if uu____18426
                                 then
                                   let uu____18431 =
                                     FStar_Syntax_Print.comp_to_string c1  in
                                   FStar_Util.print1 "} Lifted comp: %s\n"
                                     uu____18431
                                 else ());
                                (let uu____18436 =
                                   FStar_TypeChecker_Env.conj_guard g guard_f
                                    in
                                 (c1, uu____18436))))))))
  
let lift_tf_layered_effect_term :
  'Auu____18450 .
    'Auu____18450 ->
      FStar_Syntax_Syntax.sub_eff ->
        FStar_Syntax_Syntax.universe ->
          FStar_Syntax_Syntax.typ ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun sub1  ->
      fun u  ->
        fun a  ->
          fun e  ->
            let lift =
              let uu____18479 =
                let uu____18484 =
                  FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____18484
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____18479 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____18527 =
                let uu____18528 =
                  let uu____18531 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____18531
                    FStar_Syntax_Subst.compress
                   in
                uu____18528.FStar_Syntax_Syntax.n  in
              match uu____18527 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____18554::bs,uu____18556)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____18596 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____18596
                    FStar_Pervasives_Native.fst
              | uu____18702 ->
                  let uu____18703 =
                    let uu____18709 =
                      let uu____18711 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____18711
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____18709)  in
                  FStar_Errors.raise_error uu____18703
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____18738 = FStar_Syntax_Syntax.as_arg a  in
              let uu____18747 =
                let uu____18758 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____18794  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____18801 =
                  let uu____18812 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____18812]  in
                FStar_List.append uu____18758 uu____18801  in
              uu____18738 :: uu____18747  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub1  ->
      let uu____18876 =
        (let uu____18880 =
           FStar_All.pipe_right sub1.FStar_Syntax_Syntax.source
             (FStar_TypeChecker_Env.norm_eff_name env)
            in
         FStar_All.pipe_right uu____18880
           (FStar_TypeChecker_Env.is_layered_effect env))
          ||
          (FStar_All.pipe_right sub1.FStar_Syntax_Syntax.target
             (FStar_TypeChecker_Env.is_layered_effect env))
         in
      if uu____18876
      then
        let uu____18884 =
          let uu____18897 =
            FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub1.FStar_Syntax_Syntax.target uu____18897
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____18884;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub1))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____18932 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____18932 with
           | (uu____18941,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____18960 =
                 let uu____18961 =
                   let uu___2295_18962 = ct  in
                   let uu____18963 =
                     let uu____18974 =
                       let uu____18983 =
                         let uu____18984 =
                           let uu____18991 =
                             let uu____18992 =
                               let uu____19009 =
                                 let uu____19020 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____19020; wp]  in
                               (lift_t, uu____19009)  in
                             FStar_Syntax_Syntax.Tm_app uu____18992  in
                           FStar_Syntax_Syntax.mk uu____18991  in
                         uu____18984 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____18983
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____18974]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2295_18962.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub1.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2295_18962.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____18963;
                     FStar_Syntax_Syntax.flags =
                       (uu___2295_18962.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____18961  in
               (uu____18960, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____19120 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____19120 with
           | (uu____19127,lift_t) ->
               let uu____19129 =
                 let uu____19136 =
                   let uu____19137 =
                     let uu____19154 =
                       let uu____19165 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____19174 =
                         let uu____19185 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____19194 =
                           let uu____19205 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____19205]  in
                         uu____19185 :: uu____19194  in
                       uu____19165 :: uu____19174  in
                     (lift_t, uu____19154)  in
                   FStar_Syntax_Syntax.Tm_app uu____19137  in
                 FStar_Syntax_Syntax.mk uu____19136  in
               uu____19129 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____19258 =
           let uu____19271 =
             FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____19271 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____19258;
           FStar_TypeChecker_Env.mlift_term =
             (match sub1.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____19307  ->
                        fun uu____19308  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index1  ->
        let uu____19338 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____19338 with
        | (uu____19343,t) ->
            let err n1 =
              let uu____19353 =
                let uu____19359 =
                  let uu____19361 = FStar_Ident.string_of_lid datacon  in
                  let uu____19363 = FStar_Util.string_of_int n1  in
                  let uu____19365 = FStar_Util.string_of_int index1  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____19361 uu____19363 uu____19365
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____19359)
                 in
              let uu____19369 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____19353 uu____19369  in
            let uu____19370 =
              let uu____19371 = FStar_Syntax_Subst.compress t  in
              uu____19371.FStar_Syntax_Syntax.n  in
            (match uu____19370 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____19375) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____19430  ->
                           match uu____19430 with
                           | (uu____19438,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____19447 -> true)))
                    in
                 if (FStar_List.length bs1) <= index1
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index1  in
                    let uu____19479 =
                      FStar_Syntax_Util.mk_field_projector_name datacon
                        (FStar_Pervasives_Native.fst b) index1
                       in
                    FStar_All.pipe_right uu____19479
                      FStar_Pervasives_Native.fst)
             | uu____19490 -> err Prims.int_zero)
  