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
  
type join_effects_t =
  (FStar_Ident.lident * FStar_TypeChecker_Env.lift_comp_t *
    FStar_TypeChecker_Env.lift_comp_t)
let (join_layered :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> join_effects_t)
  =
  fun env  ->
    fun l  ->
      fun m  ->
        (let uu____1116 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "LayeredEffects")
            in
         if uu____1116
         then
           let uu____1121 = FStar_Ident.string_of_lid l  in
           let uu____1123 = FStar_Ident.string_of_lid m  in
           FStar_Util.print2 "join_layered::l = %s, m = %s\n" uu____1121
             uu____1123
         else ());
        (let rec aux m1 f_m =
           (let uu____1171 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "LayeredEffects")
               in
            if uu____1171
            then
              let uu____1176 = FStar_Ident.string_of_lid m1  in
              FStar_Util.print1 "enter join_layered_aux::m = %s\n" uu____1176
            else ());
           (let uu____1181 = FStar_TypeChecker_Env.join_opt env l m1  in
            match uu____1181 with
            | FStar_Pervasives_Native.None  ->
                let uu____1222 =
                  FStar_TypeChecker_Env.lookup_effect_abbrev env
                    [FStar_Syntax_Syntax.U_unknown] m1
                   in
                (match uu____1222 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____1259 =
                       let uu____1265 =
                         let uu____1267 = FStar_Syntax_Print.lid_to_string l
                            in
                         let uu____1269 = FStar_Syntax_Print.lid_to_string m1
                            in
                         FStar_Util.format2
                           "Effects %s and %s cannot be composed" uu____1267
                           uu____1269
                          in
                       (FStar_Errors.Fatal_EffectsCannotBeComposed,
                         uu____1265)
                        in
                     FStar_Errors.raise_error uu____1259
                       env.FStar_TypeChecker_Env.range
                 | FStar_Pervasives_Native.Some (uu____1299,c) ->
                     let m2 = FStar_Syntax_Util.comp_effect_name c  in
                     ((let uu____1307 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LayeredEffects")
                          in
                       if uu____1307
                       then
                         let uu____1312 = FStar_Ident.string_of_lid m2  in
                         FStar_Util.print1
                           "join_layered_aux::unfolded to m = %s\n"
                           uu____1312
                       else ());
                      aux m2
                        (fun c1  ->
                           let uu____1320 =
                             let uu____1326 = FStar_All.pipe_right c1 f_m  in
                             FStar_All.pipe_right uu____1326
                               (FStar_TypeChecker_Env.unfold_effect_abbrev_one_step
                                  env)
                              in
                           FStar_All.pipe_right uu____1320
                             FStar_Pervasives_Native.fst)))
            | FStar_Pervasives_Native.Some (n1,lift1,lift2) ->
                (n1, (lift1.FStar_TypeChecker_Env.mlift_wp),
                  ((fun en  ->
                      fun c  ->
                        let uu____1372 = FStar_All.pipe_right c f_m  in
                        FStar_All.pipe_right uu____1372
                          (lift2.FStar_TypeChecker_Env.mlift_wp en)))))
            in
         aux m (fun c  -> c))
  
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
          let uu____1421 =
            let uu____1422 =
              FStar_All.pipe_right c
                (FStar_TypeChecker_Env.unfold_effect_abbrev en)
               in
            FStar_All.pipe_right uu____1422 FStar_Syntax_Syntax.mk_Comp  in
          FStar_All.pipe_right uu____1421 (f en)  in
        let uu____1427 =
          let uu____1432 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____1433 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          (uu____1432, uu____1433)  in
        match uu____1427 with
        | (norm_l1,norm_l2) ->
            let uu____1446 =
              let uu____1453 =
                FStar_TypeChecker_Env.is_layered_effect env norm_l1  in
              let uu____1455 =
                FStar_TypeChecker_Env.is_layered_effect env norm_l2  in
              (uu____1453, uu____1455)  in
            (match uu____1446 with
             | (l1_layered,l2_layered) ->
                 if
                   (l1_layered && l2_layered) ||
                     ((Prims.op_Negation l1_layered) &&
                        (Prims.op_Negation l2_layered))
                 then
                   let uu____1486 =
                     FStar_TypeChecker_Env.join env norm_l1 norm_l2  in
                   (match uu____1486 with
                    | (m,lift1,lift2) ->
                        let uu____1506 =
                          unfold_first lift1.FStar_TypeChecker_Env.mlift_wp
                           in
                        let uu____1511 =
                          unfold_first lift2.FStar_TypeChecker_Env.mlift_wp
                           in
                        (m, uu____1506, uu____1511))
                 else
                   (let uu____1522 =
                      if l1_layered
                      then (norm_l1, l2, false)
                      else (norm_l2, l1, true)  in
                    match uu____1522 with
                    | (norm_l,m,flip) ->
                        let uu____1559 = join_layered env norm_l m  in
                        (match uu____1559 with
                         | (m1,lift1,lift2) ->
                             if flip
                             then
                               let uu____1592 = unfold_first lift1  in
                               (m1, lift2, uu____1592)
                             else
                               (let uu____1603 = unfold_first lift1  in
                                (m1, uu____1603, lift2)))))
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____1628 = join env l1 l2  in
        match uu____1628 with | (m,uu____1640,uu____1641) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp ->
        (FStar_Ident.lident * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____1674 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2)
           in
        if uu____1674
        then
          (FStar_Parser_Const.effect_Tot_lid,
            FStar_TypeChecker_Env.trivial_guard)
        else
          (let uu____1683 =
             let uu____1688 =
               FStar_All.pipe_right c1 FStar_TypeChecker_Common.lcomp_comp
                in
             FStar_All.pipe_right uu____1688
               (fun uu____1714  ->
                  match uu____1714 with
                  | (c,g) -> ((FStar_Syntax_Util.comp_effect_name c), g))
              in
           match uu____1683 with
           | (l1,g1) ->
               let uu____1737 =
                 let uu____1742 =
                   FStar_All.pipe_right c2
                     FStar_TypeChecker_Common.lcomp_comp
                    in
                 FStar_All.pipe_right uu____1742
                   (fun uu____1768  ->
                      match uu____1768 with
                      | (c,g) -> ((FStar_Syntax_Util.comp_effect_name c), g))
                  in
               (match uu____1737 with
                | (l2,g2) ->
                    let uu____1791 = join_effects env l1 l2  in
                    let uu____1792 = FStar_TypeChecker_Env.conj_guard g1 g2
                       in
                    (uu____1791, uu____1792)))
  
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
            let uu____1841 =
              let uu____1846 = FStar_TypeChecker_Env.comp_to_comp_typ env c1
                 in
              let uu____1847 = FStar_TypeChecker_Env.comp_to_comp_typ env c2
                 in
              (uu____1846, uu____1847)  in
            match uu____1841 with
            | (c11,c21) ->
                let uu____1858 =
                  join env c11.FStar_Syntax_Syntax.effect_name
                    c21.FStar_Syntax_Syntax.effect_name
                   in
                (match uu____1858 with
                 | (m,lift1,lift2) ->
                     let uu____1888 = lift_comp env c11 lift1  in
                     (match uu____1888 with
                      | (c12,g1) ->
                          let uu____1903 =
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
                               let uu____1942 = lift_comp env_x c21 lift2  in
                               match uu____1942 with
                               | (c22,g2) ->
                                   let uu____1953 =
                                     FStar_TypeChecker_Env.close_guard env
                                       [x_a] g2
                                      in
                                   (c22, uu____1953))
                             in
                          (match uu____1903 with
                           | (c22,g2) ->
                               let uu____1976 =
                                 FStar_TypeChecker_Env.conj_guard g1 g2  in
                               (m, c12, c22, uu____1976))))
  
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
            let uu____2037 =
              let uu____2038 =
                let uu____2049 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____2049]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____2038;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____2037
  
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
          let uu____2133 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____2133
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2145 =
      let uu____2146 = FStar_Syntax_Subst.compress t  in
      uu____2146.FStar_Syntax_Syntax.n  in
    match uu____2145 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2150 -> true
    | uu____2166 -> false
  
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
              let uu____2236 =
                let uu____2238 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____2238  in
              if uu____2236
              then f
              else (let uu____2245 = reason1 ()  in label uu____2245 r f)
  
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
            let uu___315_2266 = g  in
            let uu____2267 =
              let uu____2268 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____2268  in
            {
              FStar_TypeChecker_Common.guard_f = uu____2267;
              FStar_TypeChecker_Common.deferred =
                (uu___315_2266.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___315_2266.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___315_2266.FStar_TypeChecker_Common.implicits)
            }
  
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2289 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____2289
        then c
        else
          (let uu____2294 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____2294
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close1 =
                  let uu____2336 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator
                     in
                  FStar_All.pipe_right uu____2336 FStar_Util.must  in
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____2364 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____2364]  in
                       let us =
                         let uu____2386 =
                           let uu____2389 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____2389]  in
                         u_res :: uu____2386  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____2395 =
                         let uu____2400 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md close1
                            in
                         let uu____2401 =
                           let uu____2402 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____2411 =
                             let uu____2422 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____2431 =
                               let uu____2442 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____2442]  in
                             uu____2422 :: uu____2431  in
                           uu____2402 :: uu____2411  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2400 uu____2401
                          in
                       uu____2395 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____2484 = destruct_wp_comp c1  in
              match uu____2484 with
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
                let uu____2524 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____2524
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
                  let uu____2574 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs)
                     in
                  FStar_All.pipe_right uu____2574
                    (close_guard_implicits env false bs)))
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_2587  ->
            match uu___0_2587 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____2590 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____2615 =
            let uu____2618 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____2618 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____2615
            (fun c  ->
               (let uu____2674 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____2674) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____2678 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____2678)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____2689 = FStar_Syntax_Util.head_and_args' e  in
                match uu____2689 with
                | (head1,uu____2706) ->
                    let uu____2727 =
                      let uu____2728 = FStar_Syntax_Util.un_uinst head1  in
                      uu____2728.FStar_Syntax_Syntax.n  in
                    (match uu____2727 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2733 =
                           let uu____2735 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____2735
                            in
                         Prims.op_Negation uu____2733
                     | uu____2736 -> true)))
              &&
              (let uu____2739 = should_not_inline_lc lc  in
               Prims.op_Negation uu____2739)
  
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
            let uu____2767 =
              let uu____2769 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____2769  in
            if uu____2767
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____2776 = FStar_Syntax_Util.is_unit t  in
               if uu____2776
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
                    let uu____2785 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____2785
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____2790 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____2790 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let ret_wp =
                             FStar_All.pipe_right m
                               FStar_Syntax_Util.get_return_vc_combinator
                              in
                           let uu____2801 =
                             let uu____2802 =
                               let uu____2807 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m ret_wp
                                  in
                               let uu____2808 =
                                 let uu____2809 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____2818 =
                                   let uu____2829 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____2829]  in
                                 uu____2809 :: uu____2818  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____2807
                                 uu____2808
                                in
                             uu____2802 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____2801)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____2863 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____2863
           then
             let uu____2868 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____2870 = FStar_Syntax_Print.term_to_string v1  in
             let uu____2872 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____2868 uu____2870 uu____2872
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
                (let uu____2930 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____2930
                 then
                   let uu____2935 =
                     let uu____2937 = FStar_Syntax_Syntax.mk_Comp ct1  in
                     FStar_Syntax_Print.comp_to_string uu____2937  in
                   let uu____2938 =
                     let uu____2940 = FStar_Syntax_Syntax.mk_Comp ct2  in
                     FStar_Syntax_Print.comp_to_string uu____2940  in
                   FStar_Util.print2 "Binding c1:%s and c2:%s {\n" uu____2935
                     uu____2938
                 else ());
                (let ed = FStar_TypeChecker_Env.get_effect_decl env m  in
                 let uu____2945 =
                   let uu____2956 =
                     FStar_List.hd ct1.FStar_Syntax_Syntax.comp_univs  in
                   let uu____2957 =
                     FStar_List.map FStar_Pervasives_Native.fst
                       ct1.FStar_Syntax_Syntax.effect_args
                      in
                   (uu____2956, (ct1.FStar_Syntax_Syntax.result_typ),
                     uu____2957)
                    in
                 match uu____2945 with
                 | (u1,t1,is1) ->
                     let uu____2991 =
                       let uu____3002 =
                         FStar_List.hd ct2.FStar_Syntax_Syntax.comp_univs  in
                       let uu____3003 =
                         FStar_List.map FStar_Pervasives_Native.fst
                           ct2.FStar_Syntax_Syntax.effect_args
                          in
                       (uu____3002, (ct2.FStar_Syntax_Syntax.result_typ),
                         uu____3003)
                        in
                     (match uu____2991 with
                      | (u2,t2,is2) ->
                          let uu____3037 =
                            let uu____3042 =
                              FStar_All.pipe_right ed
                                FStar_Syntax_Util.get_bind_vc_combinator
                               in
                            FStar_TypeChecker_Env.inst_tscheme_with
                              uu____3042 [u1; u2]
                             in
                          (match uu____3037 with
                           | (uu____3047,bind_t) ->
                               let bind_t_shape_error s =
                                 let uu____3062 =
                                   let uu____3064 =
                                     FStar_Syntax_Print.term_to_string bind_t
                                      in
                                   FStar_Util.format2
                                     "bind %s does not have proper shape (reason:%s)"
                                     uu____3064 s
                                    in
                                 (FStar_Errors.Fatal_UnexpectedEffect,
                                   uu____3062)
                                  in
                               let uu____3068 =
                                 let uu____3113 =
                                   let uu____3114 =
                                     FStar_Syntax_Subst.compress bind_t  in
                                   uu____3114.FStar_Syntax_Syntax.n  in
                                 match uu____3113 with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (4))
                                     ->
                                     let uu____3190 =
                                       FStar_Syntax_Subst.open_comp bs c  in
                                     (match uu____3190 with
                                      | (a_b::b_b::bs1,c1) ->
                                          let uu____3275 =
                                            let uu____3302 =
                                              FStar_List.splitAt
                                                ((FStar_List.length bs1) -
                                                   (Prims.of_int (2))) bs1
                                               in
                                            FStar_All.pipe_right uu____3302
                                              (fun uu____3387  ->
                                                 match uu____3387 with
                                                 | (l1,l2) ->
                                                     let uu____3468 =
                                                       FStar_List.hd l2  in
                                                     let uu____3481 =
                                                       let uu____3488 =
                                                         FStar_List.tl l2  in
                                                       FStar_List.hd
                                                         uu____3488
                                                        in
                                                     (l1, uu____3468,
                                                       uu____3481))
                                             in
                                          (match uu____3275 with
                                           | (rest_bs,f_b,g_b) ->
                                               let uu____3616 =
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                   c1
                                                  in
                                               (a_b, b_b, rest_bs, f_b, g_b,
                                                 uu____3616)))
                                 | uu____3649 ->
                                     let uu____3650 =
                                       bind_t_shape_error
                                         "Either not an arrow or not enough binders"
                                        in
                                     FStar_Errors.raise_error uu____3650 r1
                                  in
                               (match uu____3068 with
                                | (a_b,b_b,rest_bs,f_b,g_b,bind_ct) ->
                                    let uu____3775 =
                                      let uu____3782 =
                                        let uu____3783 =
                                          let uu____3784 =
                                            let uu____3791 =
                                              FStar_All.pipe_right a_b
                                                FStar_Pervasives_Native.fst
                                               in
                                            (uu____3791, t1)  in
                                          FStar_Syntax_Syntax.NT uu____3784
                                           in
                                        let uu____3802 =
                                          let uu____3805 =
                                            let uu____3806 =
                                              let uu____3813 =
                                                FStar_All.pipe_right b_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____3813, t2)  in
                                            FStar_Syntax_Syntax.NT uu____3806
                                             in
                                          [uu____3805]  in
                                        uu____3783 :: uu____3802  in
                                      FStar_TypeChecker_Env.uvars_for_binders
                                        env rest_bs uu____3782
                                        (fun b1  ->
                                           let uu____3828 =
                                             FStar_Syntax_Print.binder_to_string
                                               b1
                                              in
                                           let uu____3830 =
                                             FStar_Range.string_of_range r1
                                              in
                                           FStar_Util.format3
                                             "implicit var for binder %s of %s:bind at %s"
                                             uu____3828
                                             (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                             uu____3830) r1
                                       in
                                    (match uu____3775 with
                                     | (rest_bs_uvars,g_uvars) ->
                                         let subst1 =
                                           FStar_List.map2
                                             (fun b1  ->
                                                fun t  ->
                                                  let uu____3867 =
                                                    let uu____3874 =
                                                      FStar_All.pipe_right b1
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    (uu____3874, t)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____3867) (a_b :: b_b
                                             :: rest_bs) (t1 :: t2 ::
                                             rest_bs_uvars)
                                            in
                                         let f_guard =
                                           let f_sort_is =
                                             let uu____3901 =
                                               let uu____3902 =
                                                 let uu____3905 =
                                                   let uu____3906 =
                                                     FStar_All.pipe_right f_b
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   uu____3906.FStar_Syntax_Syntax.sort
                                                    in
                                                 FStar_Syntax_Subst.compress
                                                   uu____3905
                                                  in
                                               uu____3902.FStar_Syntax_Syntax.n
                                                in
                                             match uu____3901 with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____3917,uu____3918::is)
                                                 ->
                                                 let uu____3960 =
                                                   FStar_All.pipe_right is
                                                     (FStar_List.map
                                                        FStar_Pervasives_Native.fst)
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3960
                                                   (FStar_List.map
                                                      (FStar_Syntax_Subst.subst
                                                         subst1))
                                             | uu____3993 ->
                                                 let uu____3994 =
                                                   bind_t_shape_error
                                                     "f's type is not a repr type"
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____3994 r1
                                              in
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun i1  ->
                                                  fun f_i1  ->
                                                    let uu____4010 =
                                                      FStar_TypeChecker_Rel.teq
                                                        env i1 f_i1
                                                       in
                                                    FStar_TypeChecker_Env.conj_guard
                                                      g uu____4010)
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
                                             let uu____4029 =
                                               let uu____4030 =
                                                 let uu____4033 =
                                                   let uu____4034 =
                                                     FStar_All.pipe_right g_b
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   uu____4034.FStar_Syntax_Syntax.sort
                                                    in
                                                 FStar_Syntax_Subst.compress
                                                   uu____4033
                                                  in
                                               uu____4030.FStar_Syntax_Syntax.n
                                                in
                                             match uu____4029 with
                                             | FStar_Syntax_Syntax.Tm_arrow
                                                 (bs,c) ->
                                                 let uu____4067 =
                                                   FStar_Syntax_Subst.open_comp
                                                     bs c
                                                    in
                                                 (match uu____4067 with
                                                  | (bs1,c1) ->
                                                      let bs_subst =
                                                        let uu____4077 =
                                                          let uu____4084 =
                                                            let uu____4085 =
                                                              FStar_List.hd
                                                                bs1
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____4085
                                                              FStar_Pervasives_Native.fst
                                                             in
                                                          let uu____4106 =
                                                            let uu____4109 =
                                                              FStar_All.pipe_right
                                                                x_a
                                                                FStar_Pervasives_Native.fst
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____4109
                                                              FStar_Syntax_Syntax.bv_to_name
                                                             in
                                                          (uu____4084,
                                                            uu____4106)
                                                           in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____4077
                                                         in
                                                      let c2 =
                                                        FStar_Syntax_Subst.subst_comp
                                                          [bs_subst] c1
                                                         in
                                                      let uu____4123 =
                                                        let uu____4124 =
                                                          FStar_Syntax_Subst.compress
                                                            (FStar_Syntax_Util.comp_result
                                                               c2)
                                                           in
                                                        uu____4124.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____4123 with
                                                       | FStar_Syntax_Syntax.Tm_app
                                                           (uu____4129,uu____4130::is)
                                                           ->
                                                           let uu____4172 =
                                                             FStar_All.pipe_right
                                                               is
                                                               (FStar_List.map
                                                                  FStar_Pervasives_Native.fst)
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____4172
                                                             (FStar_List.map
                                                                (FStar_Syntax_Subst.subst
                                                                   subst1))
                                                       | uu____4205 ->
                                                           let uu____4206 =
                                                             bind_t_shape_error
                                                               "g's type is not a repr type"
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4206 r1))
                                             | uu____4215 ->
                                                 let uu____4216 =
                                                   bind_t_shape_error
                                                     "g's type is not an arrow"
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____4216 r1
                                              in
                                           let env_g =
                                             FStar_TypeChecker_Env.push_binders
                                               env [x_a]
                                              in
                                           let uu____4238 =
                                             FStar_List.fold_left2
                                               (fun g  ->
                                                  fun i1  ->
                                                    fun g_i1  ->
                                                      let uu____4246 =
                                                        FStar_TypeChecker_Rel.teq
                                                          env_g i1 g_i1
                                                         in
                                                      FStar_TypeChecker_Env.conj_guard
                                                        g uu____4246)
                                               FStar_TypeChecker_Env.trivial_guard
                                               is2 g_sort_is
                                              in
                                           FStar_All.pipe_right uu____4238
                                             (FStar_TypeChecker_Env.close_guard
                                                env [x_a])
                                            in
                                         let is =
                                           let uu____4262 =
                                             let uu____4263 =
                                               FStar_Syntax_Subst.compress
                                                 bind_ct.FStar_Syntax_Syntax.result_typ
                                                in
                                             uu____4263.FStar_Syntax_Syntax.n
                                              in
                                           match uu____4262 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____4268,uu____4269::is) ->
                                               let uu____4311 =
                                                 FStar_All.pipe_right is
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_All.pipe_right
                                                 uu____4311
                                                 (FStar_List.map
                                                    (FStar_Syntax_Subst.subst
                                                       subst1))
                                           | uu____4344 ->
                                               let uu____4345 =
                                                 bind_t_shape_error
                                                   "return type is not a repr type"
                                                  in
                                               FStar_Errors.raise_error
                                                 uu____4345 r1
                                            in
                                         let c =
                                           let uu____4355 =
                                             let uu____4356 =
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
                                                 = uu____4356;
                                               FStar_Syntax_Syntax.flags =
                                                 flags
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____4355
                                            in
                                         ((let uu____4376 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env)
                                               (FStar_Options.Other
                                                  "LayeredEffects")
                                              in
                                           if uu____4376
                                           then
                                             let uu____4381 =
                                               FStar_Syntax_Print.comp_to_string
                                                 c
                                                in
                                             FStar_Util.print1
                                               "} c after bind: %s\n"
                                               uu____4381
                                           else ());
                                          (let uu____4386 =
                                             FStar_TypeChecker_Env.conj_guards
                                               [g_uvars; f_guard; g_guard]
                                              in
                                           (c, uu____4386))))))))
  
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
                let uu____4431 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____4457 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____4457 with
                  | (a,kwp) ->
                      let uu____4488 = destruct_wp_comp ct1  in
                      let uu____4495 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____4488, uu____4495)
                   in
                match uu____4431 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____4548 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____4548]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____4568 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____4568]
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
                      let uu____4615 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____4624 =
                        let uu____4635 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____4644 =
                          let uu____4655 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____4664 =
                            let uu____4675 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____4684 =
                              let uu____4695 =
                                let uu____4704 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____4704  in
                              [uu____4695]  in
                            uu____4675 :: uu____4684  in
                          uu____4655 :: uu____4664  in
                        uu____4635 :: uu____4644  in
                      uu____4615 :: uu____4624  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____4757 =
                        let uu____4762 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_t1; u_t2] env md bind_wp
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____4762 wp_args  in
                      uu____4757 FStar_Pervasives_Native.None
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
              let uu____4810 = lift_comps env c1 c2 b true  in
              match uu____4810 with
              | (m,c11,c21,g_lift) ->
                  let uu____4828 =
                    let uu____4833 = FStar_Syntax_Util.comp_to_comp_typ c11
                       in
                    let uu____4834 = FStar_Syntax_Util.comp_to_comp_typ c21
                       in
                    (uu____4833, uu____4834)  in
                  (match uu____4828 with
                   | (ct1,ct2) ->
                       let uu____4841 =
                         let uu____4846 =
                           FStar_TypeChecker_Env.is_layered_effect env m  in
                         if uu____4846
                         then mk_layered_bind env m ct1 b ct2 flags r1
                         else
                           (let uu____4855 =
                              mk_non_layered_bind env m ct1 b ct2 flags r1
                               in
                            (uu____4855, FStar_TypeChecker_Env.trivial_guard))
                          in
                       (match uu____4841 with
                        | (c,g_bind) ->
                            let uu____4862 =
                              FStar_TypeChecker_Env.conj_guard g_lift g_bind
                               in
                            (c, uu____4862)))
  
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
            let uu____4898 =
              let uu____4899 =
                let uu____4910 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____4910]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____4899;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4898  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____4955 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_4961  ->
              match uu___1_4961 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____4964 -> false))
       in
    if uu____4955
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_4976  ->
              match uu___2_4976 with
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
        let uu____5004 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5004
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____5015 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____5015  in
           let pure_assume_wp1 =
             let uu____5020 = FStar_TypeChecker_Env.get_range env  in
             let uu____5021 =
               let uu____5026 =
                 let uu____5027 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____5027]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____5026  in
             uu____5021 FStar_Pervasives_Native.None uu____5020  in
           let uu____5060 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____5060)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5088 =
          let uu____5089 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5089 with
          | (c,g_c) ->
              let uu____5100 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5100
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5114 = weaken_comp env c f1  in
                     (match uu____5114 with
                      | (c1,g_w) ->
                          let uu____5125 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____5125)))
           in
        let uu____5126 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5126 weaken
  
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
                 let uu____5183 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____5183  in
               let pure_assert_wp1 =
                 let uu____5188 =
                   let uu____5193 =
                     let uu____5194 =
                       let uu____5203 = label_opt env reason r f  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                         uu____5203
                        in
                     [uu____5194]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____5193
                    in
                 uu____5188 FStar_Pervasives_Native.None r  in
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
            let uu____5273 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____5273
            then (lc, g0)
            else
              (let flags =
                 let uu____5285 =
                   let uu____5293 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____5293
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5285 with
                 | (maybe_trivial_post,flags) ->
                     let uu____5323 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_5331  ->
                               match uu___3_5331 with
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
                               | uu____5334 -> []))
                        in
                     FStar_List.append flags uu____5323
                  in
               let strengthen uu____5344 =
                 let uu____5345 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____5345 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____5364 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____5364 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____5371 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____5371
                              then
                                let uu____5375 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____5377 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____5375 uu____5377
                              else ());
                             (let uu____5382 =
                                strengthen_comp env reason c f flags  in
                              match uu____5382 with
                              | (c1,g_s) ->
                                  let uu____5393 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____5393))))
                  in
               let uu____5394 =
                 FStar_TypeChecker_Common.mk_lcomp
                   lc.FStar_TypeChecker_Common.eff_name
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____5394,
                 (let uu___631_5396 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___631_5396.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___631_5396.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___631_5396.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_5405  ->
            match uu___4_5405 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____5409 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____5438 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____5438
          then e
          else
            (let uu____5445 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____5448 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____5448)
                in
             if uu____5445
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
                | uu____5518 -> false  in
              if is_unit1
              then
                let uu____5525 =
                  let uu____5527 =
                    let uu____5528 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____5528
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____5527
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____5525
                 then
                   let uu____5537 =
                     FStar_Syntax_Subst.open_term
                       [(b, FStar_Pervasives_Native.None)] phi
                      in
                   match uu____5537 with
                   | (b1::[],phi1) ->
                       let phi2 =
                         let uu____5581 =
                           let uu____5584 =
                             let uu____5585 =
                               let uu____5592 =
                                 FStar_All.pipe_right b1
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____5592, FStar_Syntax_Syntax.unit_const)
                                in
                             FStar_Syntax_Syntax.NT uu____5585  in
                           [uu____5584]  in
                         FStar_Syntax_Subst.subst uu____5581 phi1  in
                       weaken_comp env c phi2
                 else
                   (let uu____5605 = close_wp_comp env [x] c  in
                    (uu____5605, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____5608 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
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
          fun uu____5636  ->
            match uu____5636 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____5656 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____5656 then f () else ()  in
                ((let uu____5664 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "LayeredEffects")
                     in
                  if uu____5664
                  then
                    FStar_Util.print2 "Enter bind with effs: %s and %s\n\n"
                      (lc1.FStar_TypeChecker_Common.eff_name).FStar_Ident.str
                      (lc2.FStar_TypeChecker_Common.eff_name).FStar_Ident.str
                  else ());
                 (let lc11 =
                    FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1
                     in
                  let lc21 =
                    FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2
                     in
                  (let uu____5675 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "LayeredEffects")
                      in
                   if uu____5675
                   then
                     FStar_Util.print2
                       "Enter bind after promotion with effs: %s and %s\n\n"
                       (lc11.FStar_TypeChecker_Common.eff_name).FStar_Ident.str
                       (lc21.FStar_TypeChecker_Common.eff_name).FStar_Ident.str
                   else ());
                  (let uu____5683 = join_lcomp env lc11 lc21  in
                   match uu____5683 with
                   | (joined_eff,g_join) ->
                       let bind_flags =
                         let uu____5693 =
                           (should_not_inline_lc lc11) ||
                             (should_not_inline_lc lc21)
                            in
                         if uu____5693
                         then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                         else
                           (let flags =
                              let uu____5703 =
                                FStar_TypeChecker_Common.is_total_lcomp lc11
                                 in
                              if uu____5703
                              then
                                let uu____5708 =
                                  FStar_TypeChecker_Common.is_total_lcomp
                                    lc21
                                   in
                                (if uu____5708
                                 then [FStar_Syntax_Syntax.TOTAL]
                                 else
                                   (let uu____5715 =
                                      FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                        lc21
                                       in
                                    if uu____5715
                                    then [FStar_Syntax_Syntax.SOMETRIVIAL]
                                    else []))
                              else
                                (let uu____5724 =
                                   (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                      lc11)
                                     &&
                                     (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                        lc21)
                                    in
                                 if uu____5724
                                 then [FStar_Syntax_Syntax.SOMETRIVIAL]
                                 else [])
                               in
                            let uu____5731 =
                              lcomp_has_trivial_postcondition lc21  in
                            if uu____5731
                            then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION ::
                              flags
                            else flags)
                          in
                       let bind_it uu____5747 =
                         let uu____5748 =
                           env.FStar_TypeChecker_Env.lax &&
                             (FStar_Options.ml_ish ())
                            in
                         if uu____5748
                         then
                           let u_t =
                             env.FStar_TypeChecker_Env.universe_of env
                               lc21.FStar_TypeChecker_Common.res_typ
                              in
                           let uu____5756 =
                             lax_mk_tot_or_comp_l joined_eff u_t
                               lc21.FStar_TypeChecker_Common.res_typ []
                              in
                           (uu____5756, FStar_TypeChecker_Env.trivial_guard)
                         else
                           (let uu____5759 =
                              FStar_TypeChecker_Common.lcomp_comp lc11  in
                            match uu____5759 with
                            | (c1,g_c1) ->
                                let uu____5770 =
                                  FStar_TypeChecker_Common.lcomp_comp lc21
                                   in
                                (match uu____5770 with
                                 | (c2,g_c2) ->
                                     (debug1
                                        (fun uu____5790  ->
                                           let uu____5791 =
                                             FStar_Syntax_Print.comp_to_string
                                               c1
                                              in
                                           let uu____5793 =
                                             match b with
                                             | FStar_Pervasives_Native.None 
                                                 -> "none"
                                             | FStar_Pervasives_Native.Some x
                                                 ->
                                                 FStar_Syntax_Print.bv_to_string
                                                   x
                                              in
                                           let uu____5798 =
                                             FStar_Syntax_Print.comp_to_string
                                               c2
                                              in
                                           FStar_Util.print3
                                             "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                             uu____5791 uu____5793 uu____5798);
                                      (let aux uu____5816 =
                                         let uu____5817 =
                                           FStar_Syntax_Util.is_trivial_wp c1
                                            in
                                         if uu____5817
                                         then
                                           match b with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Util.Inl
                                                 (c2, "trivial no binder")
                                           | FStar_Pervasives_Native.Some
                                               uu____5848 ->
                                               let uu____5849 =
                                                 FStar_Syntax_Util.is_ml_comp
                                                   c2
                                                  in
                                               (if uu____5849
                                                then
                                                  FStar_Util.Inl
                                                    (c2, "trivial ml")
                                                else
                                                  FStar_Util.Inr
                                                    "c1 trivial; but c2 is not ML")
                                         else
                                           (let uu____5881 =
                                              (FStar_Syntax_Util.is_ml_comp
                                                 c1)
                                                &&
                                                (FStar_Syntax_Util.is_ml_comp
                                                   c2)
                                               in
                                            if uu____5881
                                            then
                                              FStar_Util.Inl (c2, "both ml")
                                            else
                                              FStar_Util.Inr
                                                "c1 not trivial, and both are not ML")
                                          in
                                       let try_simplify uu____5928 =
                                         let aux_with_trivial_guard
                                           uu____5958 =
                                           let uu____5959 = aux ()  in
                                           match uu____5959 with
                                           | FStar_Util.Inl (c,reason) ->
                                               FStar_Util.Inl
                                                 (c,
                                                   FStar_TypeChecker_Env.trivial_guard,
                                                   reason)
                                           | FStar_Util.Inr reason ->
                                               FStar_Util.Inr reason
                                            in
                                         let uu____6017 =
                                           let uu____6019 =
                                             FStar_TypeChecker_Env.try_lookup_effect_lid
                                               env
                                               FStar_Parser_Const.effect_GTot_lid
                                              in
                                           FStar_Option.isNone uu____6019  in
                                         if uu____6017
                                         then
                                           let uu____6035 =
                                             (FStar_Syntax_Util.is_tot_or_gtot_comp
                                                c1)
                                               &&
                                               (FStar_Syntax_Util.is_tot_or_gtot_comp
                                                  c2)
                                              in
                                           (if uu____6035
                                            then
                                              FStar_Util.Inl
                                                (c2,
                                                  FStar_TypeChecker_Env.trivial_guard,
                                                  "Early in prims; we don't have bind yet")
                                            else
                                              (let uu____6062 =
                                                 FStar_TypeChecker_Env.get_range
                                                   env
                                                  in
                                               FStar_Errors.raise_error
                                                 (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                                   "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                                 uu____6062))
                                         else
                                           (let uu____6079 =
                                              FStar_Syntax_Util.is_total_comp
                                                c1
                                               in
                                            if uu____6079
                                            then
                                              let close1 x reason c =
                                                let x1 =
                                                  let uu___736_6125 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___736_6125.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      =
                                                      (uu___736_6125.FStar_Syntax_Syntax.index);
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (FStar_Syntax_Util.comp_result
                                                         c1)
                                                  }  in
                                                let uu____6126 =
                                                  maybe_capture_unit_refinement
                                                    env
                                                    x1.FStar_Syntax_Syntax.sort
                                                    x1 c
                                                   in
                                                match uu____6126 with
                                                | (c3,g_c) ->
                                                    FStar_Util.Inl
                                                      (c3, g_c, reason)
                                                 in
                                              match (e1opt, b) with
                                              | (FStar_Pervasives_Native.Some
                                                 e,FStar_Pervasives_Native.Some
                                                 x) ->
                                                  let uu____6184 =
                                                    FStar_All.pipe_right c2
                                                      (FStar_Syntax_Subst.subst_comp
                                                         [FStar_Syntax_Syntax.NT
                                                            (x, e)])
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____6184
                                                    (close1 x "c1 Tot")
                                              | (uu____6200,FStar_Pervasives_Native.Some
                                                 x) ->
                                                  FStar_All.pipe_right c2
                                                    (close1 x
                                                       "c1 Tot only close")
                                              | (uu____6225,uu____6226) ->
                                                  aux_with_trivial_guard ()
                                            else
                                              (let uu____6241 =
                                                 (FStar_Syntax_Util.is_tot_or_gtot_comp
                                                    c1)
                                                   &&
                                                   (FStar_Syntax_Util.is_tot_or_gtot_comp
                                                      c2)
                                                  in
                                               if uu____6241
                                               then
                                                 let uu____6256 =
                                                   let uu____6264 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       (FStar_Syntax_Util.comp_result
                                                          c2)
                                                      in
                                                   (uu____6264,
                                                     FStar_TypeChecker_Env.trivial_guard,
                                                     "both GTot")
                                                    in
                                                 FStar_Util.Inl uu____6256
                                               else aux_with_trivial_guard ()))
                                          in
                                       let uu____6277 = try_simplify ()  in
                                       match uu____6277 with
                                       | FStar_Util.Inl (c,g_c,reason) ->
                                           (debug1
                                              (fun uu____6312  ->
                                                 let uu____6313 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c
                                                    in
                                                 FStar_Util.print2
                                                   "(2) bind: Simplified (because %s) to\n\t%s\n"
                                                   reason uu____6313);
                                            (let uu____6316 =
                                               let uu____6317 =
                                                 let uu____6318 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 g_c2
                                                    in
                                                 FStar_TypeChecker_Env.conj_guard
                                                   uu____6318 g_join
                                                  in
                                               FStar_TypeChecker_Env.conj_guard
                                                 g_c uu____6317
                                                in
                                             (c, uu____6316)))
                                       | FStar_Util.Inr reason ->
                                           (debug1
                                              (fun uu____6332  ->
                                                 FStar_Util.print1
                                                   "(2) bind: Not simplified because %s\n"
                                                   reason);
                                            (let mk_bind1 c11 b1 c21 =
                                               let uu____6358 =
                                                 mk_bind env c11 b1 c21
                                                   bind_flags r1
                                                  in
                                               match uu____6358 with
                                               | (c,g_bind) ->
                                                   let uu____6369 =
                                                     let uu____6370 =
                                                       let uu____6371 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_c1 g_c2
                                                          in
                                                       FStar_TypeChecker_Env.conj_guard
                                                         uu____6371 g_join
                                                        in
                                                     FStar_TypeChecker_Env.conj_guard
                                                       uu____6370 g_bind
                                                      in
                                                   (c, uu____6369)
                                                in
                                             let mk_seq c11 b1 c21 =
                                               let uu____6396 =
                                                 let uu____6401 =
                                                   FStar_TypeChecker_Env.comp_to_comp_typ
                                                     env c11
                                                    in
                                                 let uu____6402 =
                                                   FStar_TypeChecker_Env.comp_to_comp_typ
                                                     env c21
                                                    in
                                                 (uu____6401, uu____6402)  in
                                               match uu____6396 with
                                               | (c12,c22) ->
                                                   let uu____6409 =
                                                     join env
                                                       c12.FStar_Syntax_Syntax.effect_name
                                                       c22.FStar_Syntax_Syntax.effect_name
                                                      in
                                                   (match uu____6409 with
                                                    | (m,uu____6425,lift2) ->
                                                        let uu____6435 =
                                                          lift_comp env c22
                                                            lift2
                                                           in
                                                        (match uu____6435
                                                         with
                                                         | (c23,g2) ->
                                                             let uu____6446 =
                                                               destruct_wp_comp
                                                                 c12
                                                                in
                                                             (match uu____6446
                                                              with
                                                              | (u1,t1,wp1)
                                                                  ->
                                                                  let md_pure_or_ghost
                                                                    =
                                                                    FStar_TypeChecker_Env.get_effect_decl
                                                                    env
                                                                    c12.FStar_Syntax_Syntax.effect_name
                                                                     in
                                                                  let trivial
                                                                    =
                                                                    let uu____6462
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    md_pure_or_ghost
                                                                    FStar_Syntax_Util.get_wp_trivial_combinator
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____6462
                                                                    FStar_Util.must
                                                                     in
                                                                  let vc1 =
                                                                    let uu____6472
                                                                    =
                                                                    let uu____6477
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_effect_fun_with
                                                                    [u1] env
                                                                    md_pure_or_ghost
                                                                    trivial
                                                                     in
                                                                    let uu____6478
                                                                    =
                                                                    let uu____6479
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    t1  in
                                                                    let uu____6488
                                                                    =
                                                                    let uu____6499
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp1  in
                                                                    [uu____6499]
                                                                     in
                                                                    uu____6479
                                                                    ::
                                                                    uu____6488
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____6477
                                                                    uu____6478
                                                                     in
                                                                    uu____6472
                                                                    FStar_Pervasives_Native.None
                                                                    r1  in
                                                                  let uu____6532
                                                                    =
                                                                    strengthen_comp
                                                                    env
                                                                    FStar_Pervasives_Native.None
                                                                    c23 vc1
                                                                    bind_flags
                                                                     in
                                                                  (match uu____6532
                                                                   with
                                                                   | 
                                                                   (c,g_s) ->
                                                                    let uu____6547
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guards
                                                                    [g_c1;
                                                                    g_c2;
                                                                    g_join;
                                                                    g2;
                                                                    g_s]  in
                                                                    (c,
                                                                    uu____6547)))))
                                                in
                                             let uu____6548 =
                                               let t =
                                                 FStar_Syntax_Util.comp_result
                                                   c1
                                                  in
                                               match comp_univ_opt c1 with
                                               | FStar_Pervasives_Native.None
                                                    ->
                                                   let uu____6564 =
                                                     env.FStar_TypeChecker_Env.universe_of
                                                       env t
                                                      in
                                                   (uu____6564, t)
                                               | FStar_Pervasives_Native.Some
                                                   u -> (u, t)
                                                in
                                             match uu____6548 with
                                             | (u_res_t1,res_t1) ->
                                                 let uu____6580 =
                                                   (FStar_Option.isSome b) &&
                                                     (should_return env e1opt
                                                        lc11)
                                                    in
                                                 if uu____6580
                                                 then
                                                   let e1 =
                                                     FStar_Option.get e1opt
                                                      in
                                                   let x = FStar_Option.get b
                                                      in
                                                   let uu____6589 =
                                                     FStar_Syntax_Util.is_partial_return
                                                       c1
                                                      in
                                                   (if uu____6589
                                                    then
                                                      (debug1
                                                         (fun uu____6603  ->
                                                            let uu____6604 =
                                                              FStar_TypeChecker_Normalize.term_to_string
                                                                env e1
                                                               in
                                                            let uu____6606 =
                                                              FStar_Syntax_Print.bv_to_string
                                                                x
                                                               in
                                                            FStar_Util.print2
                                                              "(3) bind (case a): Substituting %s for %s"
                                                              uu____6604
                                                              uu____6606);
                                                       (let c21 =
                                                          FStar_Syntax_Subst.subst_comp
                                                            [FStar_Syntax_Syntax.NT
                                                               (x, e1)] c2
                                                           in
                                                        mk_bind1 c1 b c21))
                                                    else
                                                      (let uu____6614 =
                                                         ((FStar_Options.vcgen_optimize_bind_as_seq
                                                             ())
                                                            &&
                                                            (lcomp_has_trivial_postcondition
                                                               lc11))
                                                           &&
                                                           (let uu____6617 =
                                                              FStar_TypeChecker_Env.try_lookup_lid
                                                                env
                                                                FStar_Parser_Const.with_type_lid
                                                               in
                                                            FStar_Option.isSome
                                                              uu____6617)
                                                          in
                                                       if uu____6614
                                                       then
                                                         let e1' =
                                                           let uu____6642 =
                                                             FStar_Options.vcgen_decorate_with_type
                                                               ()
                                                              in
                                                           if uu____6642
                                                           then
                                                             FStar_Syntax_Util.mk_with_type
                                                               u_res_t1
                                                               res_t1 e1
                                                           else e1  in
                                                         (debug1
                                                            (fun uu____6654 
                                                               ->
                                                               let uu____6655
                                                                 =
                                                                 FStar_TypeChecker_Normalize.term_to_string
                                                                   env e1'
                                                                  in
                                                               let uu____6657
                                                                 =
                                                                 FStar_Syntax_Print.bv_to_string
                                                                   x
                                                                  in
                                                               FStar_Util.print2
                                                                 "(3) bind (case b): Substituting %s for %s"
                                                                 uu____6655
                                                                 uu____6657);
                                                          (let c21 =
                                                             FStar_Syntax_Subst.subst_comp
                                                               [FStar_Syntax_Syntax.NT
                                                                  (x, e1')]
                                                               c2
                                                              in
                                                           mk_seq c1 b c21))
                                                       else
                                                         (debug1
                                                            (fun uu____6672 
                                                               ->
                                                               let uu____6673
                                                                 =
                                                                 FStar_TypeChecker_Normalize.term_to_string
                                                                   env e1
                                                                  in
                                                               let uu____6675
                                                                 =
                                                                 FStar_Syntax_Print.bv_to_string
                                                                   x
                                                                  in
                                                               FStar_Util.print2
                                                                 "(3) bind (case c): Adding equality %s = %s"
                                                                 uu____6673
                                                                 uu____6675);
                                                          (let c21 =
                                                             FStar_Syntax_Subst.subst_comp
                                                               [FStar_Syntax_Syntax.NT
                                                                  (x, e1)] c2
                                                              in
                                                           let x_eq_e =
                                                             let uu____6682 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 x
                                                                in
                                                             FStar_Syntax_Util.mk_eq2
                                                               u_res_t1
                                                               res_t1 e1
                                                               uu____6682
                                                              in
                                                           let uu____6683 =
                                                             let uu____6688 =
                                                               let uu____6689
                                                                 =
                                                                 let uu____6690
                                                                   =
                                                                   FStar_Syntax_Syntax.mk_binder
                                                                    x
                                                                    in
                                                                 [uu____6690]
                                                                  in
                                                               FStar_TypeChecker_Env.push_binders
                                                                 env
                                                                 uu____6689
                                                                in
                                                             weaken_comp
                                                               uu____6688 c21
                                                               x_eq_e
                                                              in
                                                           match uu____6683
                                                           with
                                                           | (c22,g_w) ->
                                                               let uu____6715
                                                                 =
                                                                 mk_bind1 c1
                                                                   b c22
                                                                  in
                                                               (match uu____6715
                                                                with
                                                                | (c,g_bind)
                                                                    ->
                                                                    let uu____6726
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_w
                                                                    g_bind
                                                                     in
                                                                    (c,
                                                                    uu____6726))))))
                                                 else mk_bind1 c1 b c2))))))
                          in
                       FStar_TypeChecker_Common.mk_lcomp joined_eff
                         lc21.FStar_TypeChecker_Common.res_typ bind_flags
                         bind_it)))
  
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
      | uu____6743 -> g2
  
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
            (let uu____6767 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____6767)
           in
        let flags =
          if should_return1
          then
            let uu____6775 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____6775
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____6793 =
          let uu____6794 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____6794 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____6807 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____6807
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____6815 =
                  let uu____6817 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____6817  in
                (if uu____6815
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___856_6826 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___856_6826.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___856_6826.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___856_6826.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____6827 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____6827, g_c)
                 else
                   (let uu____6830 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____6830, g_c)))
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
                   let uu____6841 =
                     let uu____6842 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____6842
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____6841
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____6845 =
                   let uu____6850 =
                     let uu____6851 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____6851
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____6850  in
                 match uu____6845 with
                 | (bind_c,g_bind) ->
                     let uu____6860 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____6861 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____6860, uu____6861))
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
            fun uu____6897  ->
              match uu____6897 with
              | (x,lc2) ->
                  ((let uu____6907 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "LayeredEffects")
                       in
                    if uu____6907
                    then
                      FStar_Util.print2
                        "maybe_return_e2_and_bind, enter effs: %s and %s\n\n"
                        (lc1.FStar_TypeChecker_Common.eff_name).FStar_Ident.str
                        (lc2.FStar_TypeChecker_Common.eff_name).FStar_Ident.str
                    else ());
                   (let lc21 =
                      let eff1 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc1.FStar_TypeChecker_Common.eff_name
                         in
                      let eff2 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc2.FStar_TypeChecker_Common.eff_name
                         in
                      let uu____6918 =
                        ((let uu____6922 = is_pure_or_ghost_effect env eff1
                             in
                          Prims.op_Negation uu____6922) ||
                           (should_not_inline_lc lc1))
                          && (is_pure_or_ghost_effect env eff2)
                         in
                      if uu____6918
                      then maybe_assume_result_eq_pure_term env e2 lc2
                      else lc2  in
                    (let uu____6928 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "LayeredEffects")
                        in
                     if uu____6928
                     then
                       FStar_Util.print2
                         "maybe_return_e2_and_bind, effs: %s and %s\n\n"
                         (lc1.FStar_TypeChecker_Common.eff_name).FStar_Ident.str
                         (lc21.FStar_TypeChecker_Common.eff_name).FStar_Ident.str
                     else ());
                    bind r env e1opt lc1 (x, lc21)))
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6949 =
        let uu____6950 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6950  in
      FStar_Syntax_Syntax.fvar uu____6949 FStar_Syntax_Syntax.delta_constant
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
                  let uu____7000 =
                    let uu____7005 =
                      let uu____7006 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____7006 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7005 [u_a]
                     in
                  match uu____7000 with
                  | (uu____7017,conjunction) ->
                      let uu____7019 =
                        let uu____7028 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____7043 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____7028, uu____7043)  in
                      (match uu____7019 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____7089 =
                               let uu____7091 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____7091 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7089)
                              in
                           let uu____7095 =
                             let uu____7140 =
                               let uu____7141 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____7141.FStar_Syntax_Syntax.n  in
                             match uu____7140 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____7190) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____7222 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____7222 with
                                  | (a_b::bs1,body1) ->
                                      let uu____7294 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____7294 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____7442 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____7442)))
                             | uu____7475 ->
                                 let uu____7476 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____7476 r
                              in
                           (match uu____7095 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____7601 =
                                  let uu____7608 =
                                    let uu____7609 =
                                      let uu____7610 =
                                        let uu____7617 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____7617, a)  in
                                      FStar_Syntax_Syntax.NT uu____7610  in
                                    [uu____7609]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____7608
                                    (fun b  ->
                                       let uu____7633 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____7635 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____7637 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____7633 uu____7635 uu____7637) r
                                   in
                                (match uu____7601 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____7675 =
                                                let uu____7682 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____7682, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____7675) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____7721 =
                                           let uu____7722 =
                                             let uu____7725 =
                                               let uu____7726 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____7726.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____7725
                                              in
                                           uu____7722.FStar_Syntax_Syntax.n
                                            in
                                         match uu____7721 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____7737,uu____7738::is) ->
                                             let uu____7780 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____7780
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____7813 ->
                                             let uu____7814 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____7814 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____7830 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____7830)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____7835 =
                                           let uu____7836 =
                                             let uu____7839 =
                                               let uu____7840 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____7840.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____7839
                                              in
                                           uu____7836.FStar_Syntax_Syntax.n
                                            in
                                         match uu____7835 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____7851,uu____7852::is) ->
                                             let uu____7894 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____7894
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____7927 ->
                                             let uu____7928 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____7928 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____7944 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____7944)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____7949 =
                                         let uu____7950 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____7950.FStar_Syntax_Syntax.n  in
                                       match uu____7949 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____7955,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8010 ->
                                           let uu____8011 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____8011 r
                                        in
                                     let uu____8020 =
                                       let uu____8021 =
                                         let uu____8022 =
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
                                             uu____8022;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____8021
                                        in
                                     let uu____8045 =
                                       let uu____8046 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8046 g_guard
                                        in
                                     (uu____8020, uu____8045))))
  
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
                fun uu____8091  ->
                  let if_then_else1 =
                    let uu____8097 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____8097 FStar_Util.must  in
                  let uu____8104 = destruct_wp_comp ct1  in
                  match uu____8104 with
                  | (uu____8115,uu____8116,wp_t) ->
                      let uu____8118 = destruct_wp_comp ct2  in
                      (match uu____8118 with
                       | (uu____8129,uu____8130,wp_e) ->
                           let wp =
                             let uu____8135 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             let uu____8136 =
                               let uu____8141 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_a] env ed if_then_else1
                                  in
                               let uu____8142 =
                                 let uu____8143 =
                                   FStar_Syntax_Syntax.as_arg a  in
                                 let uu____8152 =
                                   let uu____8163 =
                                     FStar_Syntax_Syntax.as_arg p  in
                                   let uu____8172 =
                                     let uu____8183 =
                                       FStar_Syntax_Syntax.as_arg wp_t  in
                                     let uu____8192 =
                                       let uu____8203 =
                                         FStar_Syntax_Syntax.as_arg wp_e  in
                                       [uu____8203]  in
                                     uu____8183 :: uu____8192  in
                                   uu____8163 :: uu____8172  in
                                 uu____8143 :: uu____8152  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____8141
                                 uu____8142
                                in
                             uu____8136 FStar_Pervasives_Native.None
                               uu____8135
                              in
                           let uu____8252 = mk_comp ed u_a a wp []  in
                           (uu____8252, FStar_TypeChecker_Env.trivial_guard))
  
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
               fun uu____8322  ->
                 match uu____8322 with
                 | (uu____8336,eff_label,uu____8338,uu____8339) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____8352 =
          let uu____8360 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____8398  ->
                    match uu____8398 with
                    | (uu____8413,uu____8414,flags,uu____8416) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_8433  ->
                                match uu___5_8433 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____8436 -> false))))
             in
          if uu____8360
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____8352 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____8473 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____8475 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____8475
              then
                let uu____8482 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                   in
                (uu____8482, FStar_TypeChecker_Env.trivial_guard)
              else
                (let default_case =
                   let post_k =
                     let uu____8489 =
                       let uu____8498 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____8498]  in
                     let uu____8517 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____8489 uu____8517  in
                   let kwp =
                     let uu____8523 =
                       let uu____8532 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____8532]  in
                     let uu____8551 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____8523 uu____8551  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____8558 =
                       let uu____8559 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____8559]  in
                     let uu____8578 =
                       let uu____8581 =
                         let uu____8588 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____8588
                          in
                       let uu____8589 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____8581 uu____8589  in
                     FStar_Syntax_Util.abs uu____8558 uu____8578
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
                   let uu____8613 =
                     should_not_inline_whole_match ||
                       (let uu____8616 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____8616)
                      in
                   if uu____8613 then cthen true else cthen false  in
                 let uu____8623 =
                   FStar_List.fold_right
                     (fun uu____8676  ->
                        fun uu____8677  ->
                          match (uu____8676, uu____8677) with
                          | ((g,eff_label,uu____8731,cthen),(uu____8733,celse,g_comp))
                              ->
                              let uu____8774 =
                                let uu____8779 = maybe_return eff_label cthen
                                   in
                                FStar_TypeChecker_Common.lcomp_comp
                                  uu____8779
                                 in
                              (match uu____8774 with
                               | (cthen1,gthen) ->
                                   let uu____8790 =
                                     let uu____8799 =
                                       lift_comps env cthen1 celse
                                         FStar_Pervasives_Native.None false
                                        in
                                     match uu____8799 with
                                     | (m,cthen2,celse1,g_lift) ->
                                         let md =
                                           FStar_TypeChecker_Env.get_effect_decl
                                             env m
                                            in
                                         let uu____8822 =
                                           FStar_All.pipe_right cthen2
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         let uu____8823 =
                                           FStar_All.pipe_right celse1
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         (md, uu____8822, uu____8823, g_lift)
                                      in
                                   (match uu____8790 with
                                    | (md,ct_then,ct_else,g_lift) ->
                                        let fn =
                                          let uu____8873 =
                                            FStar_All.pipe_right md
                                              FStar_Syntax_Util.is_layered
                                             in
                                          if uu____8873
                                          then mk_layered_conjunction
                                          else mk_non_layered_conjunction  in
                                        let uu____8907 =
                                          let uu____8912 =
                                            FStar_TypeChecker_Env.get_range
                                              env
                                             in
                                          fn env md u_res_t res_t g ct_then
                                            ct_else uu____8912
                                           in
                                        (match uu____8907 with
                                         | (c,g_conjunction) ->
                                             let uu____8923 =
                                               let uu____8924 =
                                                 let uu____8925 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_comp gthen
                                                    in
                                                 FStar_TypeChecker_Env.conj_guard
                                                   uu____8925 g_lift
                                                  in
                                               FStar_TypeChecker_Env.conj_guard
                                                 uu____8924 g_conjunction
                                                in
                                             ((FStar_Pervasives_Native.Some
                                                 md), c, uu____8923)))))
                     lcases
                     (FStar_Pervasives_Native.None, default_case,
                       FStar_TypeChecker_Env.trivial_guard)
                    in
                 match uu____8623 with
                 | (md,comp,g_comp) ->
                     (match lcases with
                      | [] -> (comp, g_comp)
                      | uu____8959::[] -> (comp, g_comp)
                      | uu____9002 ->
                          let uu____9019 =
                            let uu____9021 =
                              FStar_All.pipe_right md FStar_Util.must  in
                            FStar_All.pipe_right uu____9021
                              FStar_Syntax_Util.is_layered
                             in
                          if uu____9019
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
                             let uu____9034 = destruct_wp_comp comp1  in
                             match uu____9034 with
                             | (uu____9045,uu____9046,wp) ->
                                 let ite_wp =
                                   let uu____9049 =
                                     FStar_All.pipe_right md1
                                       FStar_Syntax_Util.get_wp_ite_combinator
                                      in
                                   FStar_All.pipe_right uu____9049
                                     FStar_Util.must
                                    in
                                 let wp1 =
                                   let uu____9059 =
                                     let uu____9064 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_res_t] env md1 ite_wp
                                        in
                                     let uu____9065 =
                                       let uu____9066 =
                                         FStar_Syntax_Syntax.as_arg res_t  in
                                       let uu____9075 =
                                         let uu____9086 =
                                           FStar_Syntax_Syntax.as_arg wp  in
                                         [uu____9086]  in
                                       uu____9066 :: uu____9075  in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____9064
                                       uu____9065
                                      in
                                   uu____9059 FStar_Pervasives_Native.None
                                     wp.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____9119 =
                                   mk_comp md1 u_res_t res_t wp1
                                     bind_cases_flags
                                    in
                                 (uu____9119, g_comp))))
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
          let uu____9153 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____9153 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____9169 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____9175 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____9169 uu____9175
              else
                (let uu____9184 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____9190 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____9184 uu____9190)
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
          let uu____9215 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____9215
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____9218 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____9218
        then u_res
        else
          (let is_total =
             let uu____9225 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____9225
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____9236 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____9236 with
              | FStar_Pervasives_Native.None  ->
                  let uu____9239 =
                    let uu____9245 =
                      let uu____9247 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____9247
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____9245)
                     in
                  FStar_Errors.raise_error uu____9239
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
      let uu____9271 = destruct_wp_comp ct  in
      match uu____9271 with
      | (u_t,t,wp) ->
          let vc =
            let uu____9290 = FStar_TypeChecker_Env.get_range env  in
            let uu____9291 =
              let uu____9296 =
                let uu____9297 =
                  let uu____9298 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_trivial_combinator
                     in
                  FStar_All.pipe_right uu____9298 FStar_Util.must  in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____9297
                 in
              let uu____9305 =
                let uu____9306 = FStar_Syntax_Syntax.as_arg t  in
                let uu____9315 =
                  let uu____9326 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____9326]  in
                uu____9306 :: uu____9315  in
              FStar_Syntax_Syntax.mk_Tm_app uu____9296 uu____9305  in
            uu____9291 FStar_Pervasives_Native.None uu____9290  in
          let uu____9359 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____9359)
  
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
                  let uu____9414 = FStar_TypeChecker_Env.try_lookup_lid env f
                     in
                  match uu____9414 with
                  | FStar_Pervasives_Native.Some uu____9429 ->
                      ((let uu____9447 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____9447
                        then
                          let uu____9451 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____9451
                        else ());
                       (let coercion =
                          let uu____9457 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____9457
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____9464 =
                            let uu____9465 =
                              let uu____9466 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____9466
                               in
                            (FStar_Pervasives_Native.None, uu____9465)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____9464
                           in
                        let e1 =
                          let uu____9472 =
                            let uu____9477 =
                              let uu____9478 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____9478]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____9477
                             in
                          uu____9472 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____9512 =
                          let uu____9518 =
                            let uu____9520 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____9520
                             in
                          (FStar_Errors.Warning_CoercionNotFound, uu____9518)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____9512);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____9539 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____9557 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____9568 -> false 
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
      let uu____9592 = FStar_Syntax_Util.head_and_args t2  in
      match uu____9592 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____9637 =
              let uu____9652 =
                let uu____9653 = FStar_Syntax_Subst.compress h1  in
                uu____9653.FStar_Syntax_Syntax.n  in
              (uu____9652, args)  in
            match uu____9637 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____9700,uu____9701) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____9734) -> Maybe
            | uu____9755 -> No  in
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
            (((let uu____9807 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____9807) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____9826 =
                 let uu____9827 = FStar_Syntax_Subst.compress t1  in
                 uu____9827.FStar_Syntax_Syntax.n  in
               match uu____9826 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____9832 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____9842 =
                 let uu____9843 = FStar_Syntax_Subst.compress t1  in
                 uu____9843.FStar_Syntax_Syntax.n  in
               match uu____9842 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____9848 -> false  in
             let is_type1 t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____9858 =
                 let uu____9859 = FStar_Syntax_Subst.compress t1  in
                 uu____9859.FStar_Syntax_Syntax.n  in
               match uu____9858 with
               | FStar_Syntax_Syntax.Tm_type uu____9863 -> true
               | uu____9865 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____9868 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____9868 with
             | (head1,args) ->
                 ((let uu____9918 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____9918
                   then
                     let uu____9922 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____9924 = FStar_Syntax_Print.term_to_string e  in
                     let uu____9926 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____9928 = FStar_Syntax_Print.term_to_string exp_t
                        in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____9922 uu____9924 uu____9926 uu____9928
                   else ());
                  (let mk_erased u t =
                     let uu____9946 =
                       let uu____9949 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____9949 [u]  in
                     let uu____9950 =
                       let uu____9961 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____9961]  in
                     FStar_Syntax_Util.mk_app uu____9946 uu____9950  in
                   let uu____9986 =
                     let uu____10001 =
                       let uu____10002 = FStar_Syntax_Util.un_uinst head1  in
                       uu____10002.FStar_Syntax_Syntax.n  in
                     (uu____10001, args)  in
                   match uu____9986 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type1 exp_t)
                       ->
                       let uu____10040 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____10040 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____10080 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____10080 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____10120 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____10120 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____10160 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____10160 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____10181 ->
                       let uu____10196 =
                         let uu____10201 = check_erased env res_typ  in
                         let uu____10202 = check_erased env exp_t  in
                         (uu____10201, uu____10202)  in
                       (match uu____10196 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____10211 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____10211 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____10222 =
                                   let uu____10227 =
                                     let uu____10228 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____10228]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____10227
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____10222 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____10263 =
                              let uu____10268 =
                                let uu____10269 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____10269]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____10268
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____10263 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____10302 ->
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
        let uu____10337 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____10337 with
        | (hd1,args) ->
            let uu____10386 =
              let uu____10401 =
                let uu____10402 = FStar_Syntax_Subst.compress hd1  in
                uu____10402.FStar_Syntax_Syntax.n  in
              (uu____10401, args)  in
            (match uu____10386 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____10440 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun _10467  -> FStar_Pervasives_Native.Some _10467)
                   uu____10440
             | uu____10468 -> FStar_Pervasives_Native.None)
  
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
          (let uu____10521 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____10521
           then
             let uu____10524 = FStar_Syntax_Print.term_to_string e  in
             let uu____10526 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____10528 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____10524 uu____10526 uu____10528
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____10538 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____10538 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____10563 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____10589 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____10589, false)
             else
               (let uu____10599 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____10599, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____10612) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____10624 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____10624
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1260_10640 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1260_10640.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1260_10640.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1260_10640.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____10647 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____10647 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____10663 =
                      let uu____10664 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____10664 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____10684 =
                            let uu____10686 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____10686 = FStar_Syntax_Util.Equal  in
                          if uu____10684
                          then
                            ((let uu____10693 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____10693
                              then
                                let uu____10697 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____10699 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____10697 uu____10699
                              else ());
                             (let uu____10704 = set_result_typ1 c  in
                              (uu____10704, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____10711 ->
                                   true
                               | uu____10719 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____10728 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____10728
                                  in
                               let lc1 =
                                 let uu____10730 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____10731 =
                                   let uu____10732 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____10732)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____10730 uu____10731
                                  in
                               ((let uu____10736 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____10736
                                 then
                                   let uu____10740 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____10742 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____10744 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____10746 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____10740 uu____10742 uu____10744
                                     uu____10746
                                 else ());
                                (let uu____10751 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____10751 with
                                 | (c1,g_lc) ->
                                     let uu____10762 = set_result_typ1 c1  in
                                     let uu____10763 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____10762, uu____10763)))
                             else
                               ((let uu____10767 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____10767
                                 then
                                   let uu____10771 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____10773 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____10771 uu____10773
                                 else ());
                                (let uu____10778 = set_result_typ1 c  in
                                 (uu____10778, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1297_10782 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1297_10782.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1297_10782.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1297_10782.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____10792 =
                      let uu____10793 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____10793
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____10803 =
                           let uu____10804 = FStar_Syntax_Subst.compress f1
                              in
                           uu____10804.FStar_Syntax_Syntax.n  in
                         match uu____10803 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____10811,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____10813;
                                            FStar_Syntax_Syntax.vars =
                                              uu____10814;_},uu____10815)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1313_10841 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1313_10841.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1313_10841.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1313_10841.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____10842 ->
                             let uu____10843 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____10843 with
                              | (c,g_c) ->
                                  ((let uu____10855 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____10855
                                    then
                                      let uu____10859 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____10861 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____10863 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____10865 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____10859 uu____10861 uu____10863
                                        uu____10865
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
                                        let uu____10878 =
                                          let uu____10883 =
                                            let uu____10884 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____10884]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____10883
                                           in
                                        uu____10878
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____10911 =
                                      let uu____10916 =
                                        FStar_All.pipe_left
                                          (fun _10937  ->
                                             FStar_Pervasives_Native.Some
                                               _10937)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____10938 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____10939 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____10940 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____10916
                                        uu____10938 e uu____10939 uu____10940
                                       in
                                    match uu____10911 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1331_10948 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1331_10948.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1331_10948.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____10950 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____10950
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____10953 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____10953 with
                                         | (c2,g_lc) ->
                                             ((let uu____10965 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____10965
                                               then
                                                 let uu____10969 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____10969
                                               else ());
                                              (let uu____10974 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____10974))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_10983  ->
                              match uu___6_10983 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____10986 -> []))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1347_10989 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1347_10989.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1347_10989.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1347_10989.FStar_TypeChecker_Common.implicits)
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
        let uu____11025 =
          let uu____11028 =
            let uu____11033 =
              let uu____11034 =
                let uu____11043 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____11043  in
              [uu____11034]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____11033  in
          uu____11028 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____11025  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____11066 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____11066
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____11085 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____11101 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____11118 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____11118
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____11134)::(ens,uu____11136)::uu____11137 ->
                    let uu____11180 =
                      let uu____11183 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____11183  in
                    let uu____11184 =
                      let uu____11185 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____11185  in
                    (uu____11180, uu____11184)
                | uu____11188 ->
                    let uu____11199 =
                      let uu____11205 =
                        let uu____11207 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____11207
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____11205)
                       in
                    FStar_Errors.raise_error uu____11199
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____11227)::uu____11228 ->
                    let uu____11255 =
                      let uu____11260 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____11260
                       in
                    (match uu____11255 with
                     | (us_r,uu____11292) ->
                         let uu____11293 =
                           let uu____11298 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____11298
                            in
                         (match uu____11293 with
                          | (us_e,uu____11330) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____11333 =
                                  let uu____11334 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____11334
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____11333
                                  us_r
                                 in
                              let as_ens =
                                let uu____11336 =
                                  let uu____11337 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____11337
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____11336
                                  us_e
                                 in
                              let req =
                                let uu____11341 =
                                  let uu____11346 =
                                    let uu____11347 =
                                      let uu____11358 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____11358]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____11347
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____11346
                                   in
                                uu____11341 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____11398 =
                                  let uu____11403 =
                                    let uu____11404 =
                                      let uu____11415 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____11415]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____11404
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____11403
                                   in
                                uu____11398 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____11452 =
                                let uu____11455 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____11455  in
                              let uu____11456 =
                                let uu____11457 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____11457  in
                              (uu____11452, uu____11456)))
                | uu____11460 -> failwith "Impossible"))
  
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
        (let uu____11499 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____11499
         then
           let uu____11504 = FStar_Syntax_Print.term_to_string tm  in
           let uu____11506 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____11504
             uu____11506
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
          (let uu____11565 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____11565
           then
             let uu____11570 = FStar_Syntax_Print.term_to_string tm  in
             let uu____11572 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____11570
               uu____11572
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____11583 =
      let uu____11585 =
        let uu____11586 = FStar_Syntax_Subst.compress t  in
        uu____11586.FStar_Syntax_Syntax.n  in
      match uu____11585 with
      | FStar_Syntax_Syntax.Tm_app uu____11590 -> false
      | uu____11608 -> true  in
    if uu____11583
    then t
    else
      (let uu____11613 = FStar_Syntax_Util.head_and_args t  in
       match uu____11613 with
       | (head1,args) ->
           let uu____11656 =
             let uu____11658 =
               let uu____11659 = FStar_Syntax_Subst.compress head1  in
               uu____11659.FStar_Syntax_Syntax.n  in
             match uu____11658 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____11664 -> false  in
           if uu____11656
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____11696 ->
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
          ((let uu____11743 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____11743
            then
              let uu____11746 = FStar_Syntax_Print.term_to_string e  in
              let uu____11748 = FStar_Syntax_Print.term_to_string t  in
              let uu____11750 =
                let uu____11752 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____11752
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____11746 uu____11748 uu____11750
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____11765 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____11765 with
              | (formals,uu____11781) ->
                  let n_implicits =
                    let uu____11803 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____11881  ->
                              match uu____11881 with
                              | (uu____11889,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____11896 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____11896 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____11803 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____12021 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____12021 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____12035 =
                      let uu____12041 =
                        let uu____12043 = FStar_Util.string_of_int n_expected
                           in
                        let uu____12045 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____12047 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____12043 uu____12045 uu____12047
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____12041)
                       in
                    let uu____12051 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____12035 uu____12051
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_12069 =
              match uu___7_12069 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____12112 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____12112 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _12243,uu____12230)
                           when _12243 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____12276,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____12278))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____12312 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____12312 with
                            | (v1,uu____12353,g) ->
                                ((let uu____12368 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____12368
                                  then
                                    let uu____12371 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____12371
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____12381 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____12381 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____12474 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____12474))))
                       | (uu____12501,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____12538 =
                             let uu____12551 =
                               let uu____12558 =
                                 let uu____12563 = FStar_Dyn.mkdyn env  in
                                 (uu____12563, tau)  in
                               FStar_Pervasives_Native.Some uu____12558  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____12551
                              in
                           (match uu____12538 with
                            | (v1,uu____12596,g) ->
                                ((let uu____12611 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____12611
                                  then
                                    let uu____12614 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____12614
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____12624 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____12624 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____12717 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____12717))))
                       | (uu____12744,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____12792 =
                       let uu____12819 = inst_n_binders t1  in
                       aux [] uu____12819 bs1  in
                     (match uu____12792 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____12891) -> (e, torig, guard)
                           | (uu____12922,[]) when
                               let uu____12953 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____12953 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____12955 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____12983 ->
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
            | uu____12996 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____13008 =
      let uu____13012 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____13012
        (FStar_List.map
           (fun u  ->
              let uu____13024 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____13024 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____13008 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____13052 = FStar_Util.set_is_empty x  in
      if uu____13052
      then []
      else
        (let s =
           let uu____13070 =
             let uu____13073 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____13073  in
           FStar_All.pipe_right uu____13070 FStar_Util.set_elements  in
         (let uu____13089 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____13089
          then
            let uu____13094 =
              let uu____13096 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____13096  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____13094
          else ());
         (let r =
            let uu____13105 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____13105  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____13144 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____13144
                     then
                       let uu____13149 =
                         let uu____13151 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____13151
                          in
                       let uu____13155 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____13157 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____13149 uu____13155 uu____13157
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
        let uu____13187 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____13187 FStar_Util.set_elements  in
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
        | ([],uu____13226) -> generalized_univ_names
        | (uu____13233,[]) -> explicit_univ_names
        | uu____13240 ->
            let uu____13249 =
              let uu____13255 =
                let uu____13257 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____13257
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____13255)
               in
            FStar_Errors.raise_error uu____13249 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____13279 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____13279
       then
         let uu____13284 = FStar_Syntax_Print.term_to_string t  in
         let uu____13286 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____13284 uu____13286
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____13295 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____13295
        then
          let uu____13300 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____13300
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____13309 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____13309
         then
           let uu____13314 = FStar_Syntax_Print.term_to_string t  in
           let uu____13316 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____13314 uu____13316
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
        let uu____13400 =
          let uu____13402 =
            FStar_Util.for_all
              (fun uu____13416  ->
                 match uu____13416 with
                 | (uu____13426,uu____13427,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____13402  in
        if uu____13400
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____13479 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____13479
              then
                let uu____13482 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____13482
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____13489 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____13489
               then
                 let uu____13492 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____13492
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____13510 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____13510 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____13544 =
             match uu____13544 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____13581 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____13581
                   then
                     let uu____13586 =
                       let uu____13588 =
                         let uu____13592 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____13592
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____13588
                         (FStar_String.concat ", ")
                        in
                     let uu____13640 =
                       let uu____13642 =
                         let uu____13646 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____13646
                           (FStar_List.map
                              (fun u  ->
                                 let uu____13659 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____13661 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____13659
                                   uu____13661))
                          in
                       FStar_All.pipe_right uu____13642
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____13586
                       uu____13640
                   else ());
                  (let univs2 =
                     let uu____13675 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____13687 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____13687) univs1
                       uu____13675
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____13694 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____13694
                    then
                      let uu____13699 =
                        let uu____13701 =
                          let uu____13705 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____13705
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____13701
                          (FStar_String.concat ", ")
                         in
                      let uu____13753 =
                        let uu____13755 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____13769 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____13771 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____13769
                                    uu____13771))
                           in
                        FStar_All.pipe_right uu____13755
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____13699 uu____13753
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____13792 =
             let uu____13809 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____13809  in
           match uu____13792 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____13899 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____13899
                 then ()
                 else
                   (let uu____13904 = lec_hd  in
                    match uu____13904 with
                    | (lb1,uu____13912,uu____13913) ->
                        let uu____13914 = lec2  in
                        (match uu____13914 with
                         | (lb2,uu____13922,uu____13923) ->
                             let msg =
                               let uu____13926 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____13928 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____13926 uu____13928
                                in
                             let uu____13931 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____13931))
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
                 let uu____13999 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____13999
                 then ()
                 else
                   (let uu____14004 = lec_hd  in
                    match uu____14004 with
                    | (lb1,uu____14012,uu____14013) ->
                        let uu____14014 = lec2  in
                        (match uu____14014 with
                         | (lb2,uu____14022,uu____14023) ->
                             let msg =
                               let uu____14026 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____14028 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____14026 uu____14028
                                in
                             let uu____14031 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____14031))
                  in
               let lecs1 =
                 let uu____14042 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____14095 = univs_and_uvars_of_lec this_lec  in
                        match uu____14095 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____14042 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____14200 = lec_hd  in
                   match uu____14200 with
                   | (lbname,e,c) ->
                       let uu____14210 =
                         let uu____14216 =
                           let uu____14218 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____14220 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____14222 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____14218 uu____14220 uu____14222
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____14216)
                          in
                       let uu____14226 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____14210 uu____14226
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____14245 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____14245 with
                         | FStar_Pervasives_Native.Some uu____14254 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____14262 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____14266 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____14266 with
                              | (bs,kres) ->
                                  ((let uu____14310 =
                                      let uu____14311 =
                                        let uu____14314 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____14314
                                         in
                                      uu____14311.FStar_Syntax_Syntax.n  in
                                    match uu____14310 with
                                    | FStar_Syntax_Syntax.Tm_type uu____14315
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____14319 =
                                          let uu____14321 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____14321  in
                                        if uu____14319
                                        then fail1 kres
                                        else ()
                                    | uu____14326 -> fail1 kres);
                                   (let a =
                                      let uu____14328 =
                                        let uu____14331 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _14334  ->
                                             FStar_Pervasives_Native.Some
                                               _14334) uu____14331
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____14328
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____14342 ->
                                          let uu____14351 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____14351
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
                      (fun uu____14454  ->
                         match uu____14454 with
                         | (lbname,e,c) ->
                             let uu____14500 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____14561 ->
                                   let uu____14574 = (e, c)  in
                                   (match uu____14574 with
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
                                                (fun uu____14614  ->
                                                   match uu____14614 with
                                                   | (x,uu____14620) ->
                                                       let uu____14621 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____14621)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____14639 =
                                                let uu____14641 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____14641
                                                 in
                                              if uu____14639
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
                                          let uu____14650 =
                                            let uu____14651 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____14651.FStar_Syntax_Syntax.n
                                             in
                                          match uu____14650 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____14676 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____14676 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____14687 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____14691 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____14691, gen_tvars))
                                in
                             (match uu____14500 with
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
        (let uu____14838 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____14838
         then
           let uu____14841 =
             let uu____14843 =
               FStar_List.map
                 (fun uu____14858  ->
                    match uu____14858 with
                    | (lb,uu____14867,uu____14868) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____14843 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____14841
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____14894  ->
                match uu____14894 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____14923 = gen env is_rec lecs  in
           match uu____14923 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____15022  ->
                       match uu____15022 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____15084 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____15084
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____15132  ->
                           match uu____15132 with
                           | (l,us,e,c,gvs) ->
                               let uu____15166 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____15168 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____15170 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____15172 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____15174 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____15166 uu____15168 uu____15170
                                 uu____15172 uu____15174))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____15219  ->
                match uu____15219 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____15263 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____15263, t, c, gvs)) univnames_lecs
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
              (let uu____15328 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                  in
               match uu____15328 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____15334 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _15337  -> FStar_Pervasives_Native.Some _15337)
                     uu____15334)
             in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1800_15357 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1800_15357.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1800_15357.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____15358 -> e2  in
          let uu____15359 = maybe_coerce_lc env1 e lc t2  in
          match uu____15359 with
          | (e1,lc1,g_c) ->
              let uu____15375 =
                check1 env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____15375 with
               | FStar_Pervasives_Native.None  ->
                   let uu____15384 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____15390 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____15384 uu____15390
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____15399 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____15399
                     then
                       let uu____15404 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____15404
                     else ());
                    (let uu____15410 = decorate e1 t2  in
                     let uu____15411 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (uu____15410, lc1, uu____15411))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____15439 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____15439
         then
           let uu____15442 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____15442
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____15456 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____15456 with
         | (c,g_c) ->
             let uu____15468 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____15468
             then
               let uu____15476 =
                 let uu____15478 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____15478  in
               (uu____15476, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____15486 =
                    let uu____15487 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____15487
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____15486
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____15488 = check_trivial_precondition env c1  in
                match uu____15488 with
                | (ct,vc,g_pre) ->
                    ((let uu____15504 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____15504
                      then
                        let uu____15509 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____15509
                      else ());
                     (let uu____15514 =
                        let uu____15516 =
                          let uu____15517 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____15517  in
                        discharge uu____15516  in
                      let uu____15518 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____15514, uu____15518)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_15552 =
        match uu___8_15552 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____15562)::[] -> f fst1
        | uu____15587 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____15599 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____15599
          (fun _15600  -> FStar_TypeChecker_Common.NonTrivial _15600)
         in
      let op_or_e e =
        let uu____15611 =
          let uu____15612 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____15612  in
        FStar_All.pipe_right uu____15611
          (fun _15615  -> FStar_TypeChecker_Common.NonTrivial _15615)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _15622  -> FStar_TypeChecker_Common.NonTrivial _15622)
         in
      let op_or_t t =
        let uu____15633 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____15633
          (fun _15636  -> FStar_TypeChecker_Common.NonTrivial _15636)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _15643  -> FStar_TypeChecker_Common.NonTrivial _15643)
         in
      let short_op_ite uu___9_15649 =
        match uu___9_15649 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____15659)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____15686)::[] ->
            let uu____15727 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____15727
              (fun _15728  -> FStar_TypeChecker_Common.NonTrivial _15728)
        | uu____15729 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____15741 =
          let uu____15749 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____15749)  in
        let uu____15757 =
          let uu____15767 =
            let uu____15775 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____15775)  in
          let uu____15783 =
            let uu____15793 =
              let uu____15801 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____15801)  in
            let uu____15809 =
              let uu____15819 =
                let uu____15827 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____15827)  in
              let uu____15835 =
                let uu____15845 =
                  let uu____15853 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____15853)  in
                [uu____15845; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____15819 :: uu____15835  in
            uu____15793 :: uu____15809  in
          uu____15767 :: uu____15783  in
        uu____15741 :: uu____15757  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____15915 =
            FStar_Util.find_map table
              (fun uu____15930  ->
                 match uu____15930 with
                 | (x,mk1) ->
                     let uu____15947 = FStar_Ident.lid_equals x lid  in
                     if uu____15947
                     then
                       let uu____15952 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____15952
                     else FStar_Pervasives_Native.None)
             in
          (match uu____15915 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____15956 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____15964 =
      let uu____15965 = FStar_Syntax_Util.un_uinst l  in
      uu____15965.FStar_Syntax_Syntax.n  in
    match uu____15964 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____15970 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____16006)::uu____16007 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____16026 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____16035,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____16036))::uu____16037 -> bs
      | uu____16055 ->
          let uu____16056 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____16056 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____16060 =
                 let uu____16061 = FStar_Syntax_Subst.compress t  in
                 uu____16061.FStar_Syntax_Syntax.n  in
               (match uu____16060 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____16065) ->
                    let uu____16086 =
                      FStar_Util.prefix_until
                        (fun uu___10_16126  ->
                           match uu___10_16126 with
                           | (uu____16134,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____16135)) ->
                               false
                           | uu____16140 -> true) bs'
                       in
                    (match uu____16086 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____16176,uu____16177) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____16249,uu____16250) ->
                         let uu____16323 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____16343  ->
                                   match uu____16343 with
                                   | (x,uu____16352) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____16323
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____16401  ->
                                     match uu____16401 with
                                     | (x,i) ->
                                         let uu____16420 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____16420, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____16431 -> bs))
  
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
            let uu____16460 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____16460
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
          let uu____16491 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____16491
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
        (let uu____16534 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____16534
         then
           ((let uu____16539 = FStar_Ident.text_of_lid lident  in
             d uu____16539);
            (let uu____16541 = FStar_Ident.text_of_lid lident  in
             let uu____16543 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____16541 uu____16543))
         else ());
        (let fv =
           let uu____16549 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____16549
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
         let uu____16561 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1961_16563 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1961_16563.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1961_16563.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1961_16563.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1961_16563.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___1961_16563.FStar_Syntax_Syntax.sigopts)
           }), uu____16561))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_16581 =
        match uu___11_16581 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____16584 -> false  in
      let reducibility uu___12_16592 =
        match uu___12_16592 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____16599 -> false  in
      let assumption uu___13_16607 =
        match uu___13_16607 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____16611 -> false  in
      let reification uu___14_16619 =
        match uu___14_16619 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____16622 -> true
        | uu____16624 -> false  in
      let inferred uu___15_16632 =
        match uu___15_16632 with
        | FStar_Syntax_Syntax.Discriminator uu____16634 -> true
        | FStar_Syntax_Syntax.Projector uu____16636 -> true
        | FStar_Syntax_Syntax.RecordType uu____16642 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____16652 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____16665 -> false  in
      let has_eq uu___16_16673 =
        match uu___16_16673 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____16677 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____16756 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____16763 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____16796 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____16796))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____16827 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____16827
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
           | FStar_Syntax_Syntax.Sig_bundle uu____16847 ->
               let uu____16856 =
                 let uu____16858 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_16864  ->
                           match uu___17_16864 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____16867 -> false))
                    in
                 Prims.op_Negation uu____16858  in
               if uu____16856
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____16874 -> ()
           | uu____16881 ->
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
      let uu____16895 =
        let uu____16897 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_16903  ->
                  match uu___18_16903 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____16906 -> false))
           in
        FStar_All.pipe_right uu____16897 Prims.op_Negation  in
      if uu____16895
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____16927 =
            let uu____16933 =
              let uu____16935 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____16935 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____16933)  in
          FStar_Errors.raise_error uu____16927 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____16953 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____16961 =
            let uu____16963 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____16963  in
          if uu____16961 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____16974),uu____16975) ->
              ((let uu____16987 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____16987
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____16996 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____16996
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____17007 ->
              ((let uu____17017 =
                  let uu____17019 =
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
                  Prims.op_Negation uu____17019  in
                if uu____17017 then err'1 () else ());
               (let uu____17029 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_17035  ->
                           match uu___19_17035 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____17038 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____17029
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____17044 ->
              let uu____17051 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____17051 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____17059 ->
              let uu____17066 =
                let uu____17068 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____17068  in
              if uu____17066 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____17078 ->
              let uu____17079 =
                let uu____17081 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____17081  in
              if uu____17079 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____17091 ->
              let uu____17104 =
                let uu____17106 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____17106  in
              if uu____17104 then err'1 () else ()
          | uu____17116 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____17155 =
          let uu____17156 = FStar_Syntax_Subst.compress t1  in
          uu____17156.FStar_Syntax_Syntax.n  in
        match uu____17155 with
        | FStar_Syntax_Syntax.Tm_arrow uu____17160 ->
            let uu____17175 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____17175 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____17208;
               FStar_Syntax_Syntax.index = uu____17209;
               FStar_Syntax_Syntax.sort = t2;_},uu____17211)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____17220) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____17246) ->
            descend env head1
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____17252 -> false
      
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
        (let uu____17262 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____17262
         then
           let uu____17267 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____17267
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
                  let uu____17332 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____17332 r  in
                let uu____17342 =
                  let uu____17343 = FStar_Syntax_Subst.compress signature  in
                  uu____17343.FStar_Syntax_Syntax.n  in
                match uu____17342 with
                | FStar_Syntax_Syntax.Tm_arrow (bs,uu____17351) ->
                    let bs1 = FStar_Syntax_Subst.open_binders bs  in
                    (match bs1 with
                     | a::bs2 ->
                         let uu____17399 =
                           FStar_TypeChecker_Env.uvars_for_binders env bs2
                             [FStar_Syntax_Syntax.NT
                                ((FStar_Pervasives_Native.fst a), a_tm)]
                             (fun b  ->
                                let uu____17414 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____17416 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format3
                                  "uvar for binder %s when creating a fresh repr for %s at %s"
                                  uu____17414 eff_name.FStar_Ident.str
                                  uu____17416) r
                            in
                         (match uu____17399 with
                          | (is,g) ->
                              let uu____17429 =
                                match repr_ts_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let eff_c =
                                      let uu____17431 =
                                        let uu____17432 =
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
                                            uu____17432;
                                          FStar_Syntax_Syntax.flags = []
                                        }  in
                                      FStar_Syntax_Syntax.mk_Comp uu____17431
                                       in
                                    let uu____17451 =
                                      let uu____17458 =
                                        let uu____17459 =
                                          let uu____17474 =
                                            let uu____17483 =
                                              FStar_Syntax_Syntax.null_binder
                                                FStar_Syntax_Syntax.t_unit
                                               in
                                            [uu____17483]  in
                                          (uu____17474, eff_c)  in
                                        FStar_Syntax_Syntax.Tm_arrow
                                          uu____17459
                                         in
                                      FStar_Syntax_Syntax.mk uu____17458  in
                                    uu____17451 FStar_Pervasives_Native.None
                                      r
                                | FStar_Pervasives_Native.Some repr_ts ->
                                    let repr =
                                      let uu____17514 =
                                        FStar_TypeChecker_Env.inst_tscheme_with
                                          repr_ts [u]
                                         in
                                      FStar_All.pipe_right uu____17514
                                        FStar_Pervasives_Native.snd
                                       in
                                    let uu____17523 =
                                      let uu____17528 =
                                        FStar_List.map
                                          FStar_Syntax_Syntax.as_arg (a_tm ::
                                          is)
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app repr
                                        uu____17528
                                       in
                                    uu____17523 FStar_Pervasives_Native.None
                                      r
                                 in
                              (uu____17429, g))
                     | uu____17537 -> fail1 signature)
                | uu____17538 -> fail1 signature
  
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
              let uu____17570 =
                let uu____17575 =
                  FStar_TypeChecker_Env.try_lookup_and_inst_lid env [u]
                    eff_name
                   in
                FStar_All.pipe_right uu____17575 FStar_Util.must  in
              FStar_All.pipe_right uu____17570 FStar_Pervasives_Native.fst
               in
            let repr_ts_opt =
              let uu____17603 =
                FStar_TypeChecker_Env.effect_decl_opt env eff_name  in
              FStar_Util.bind_opt uu____17603
                (fun x  ->
                   let uu____17627 =
                     FStar_All.pipe_right x FStar_Pervasives_Native.fst  in
                   FStar_All.pipe_right uu____17627
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
              let uu____17671 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____17671 with
              | (uu____17676,sig_tm) ->
                  let fail1 t =
                    let uu____17684 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____17684 r  in
                  let uu____17690 =
                    let uu____17691 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____17691.FStar_Syntax_Syntax.n  in
                  (match uu____17690 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____17695) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____17718)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____17740 -> fail1 sig_tm)
                   | uu____17741 -> fail1 sig_tm)
  
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
          (let uu____17772 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____17772
           then
             let uu____17777 = FStar_Syntax_Print.comp_to_string c  in
             let uu____17779 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____17777 uu____17779
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let effect_args_from_repr repr is_layered1 =
             let err uu____17809 =
               let uu____17810 =
                 let uu____17816 =
                   let uu____17818 = FStar_Syntax_Print.term_to_string repr
                      in
                   let uu____17820 = FStar_Util.string_of_bool is_layered1
                      in
                   FStar_Util.format2
                     "Could not get effect args from repr %s with is_layered %s"
                     uu____17818 uu____17820
                    in
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____17816)  in
               FStar_Errors.raise_error uu____17810 r  in
             let repr1 = FStar_Syntax_Subst.compress repr  in
             if is_layered1
             then
               match repr1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_app (uu____17832,uu____17833::is) ->
                   FStar_All.pipe_right is
                     (FStar_List.map FStar_Pervasives_Native.fst)
               | uu____17901 -> err ()
             else
               (match repr1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (uu____17906,c1) ->
                    let uu____17928 =
                      FStar_All.pipe_right c1
                        FStar_Syntax_Util.comp_to_comp_typ
                       in
                    FStar_All.pipe_right uu____17928
                      (fun ct  ->
                         FStar_All.pipe_right
                           ct.FStar_Syntax_Syntax.effect_args
                           (FStar_List.map FStar_Pervasives_Native.fst))
                | uu____17963 -> err ())
              in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____17965 =
             let uu____17976 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____17977 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____17976, (ct.FStar_Syntax_Syntax.result_typ), uu____17977)
              in
           match uu____17965 with
           | (u,a,c_is) ->
               let uu____18025 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____18025 with
                | (uu____18034,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____18045 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____18047 = FStar_Ident.string_of_lid tgt  in
                      let uu____18049 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____18045 uu____18047 s uu____18049
                       in
                    let uu____18052 =
                      let uu____18085 =
                        let uu____18086 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____18086.FStar_Syntax_Syntax.n  in
                      match uu____18085 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____18150 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____18150 with
                           | (a_b::bs1,c2) ->
                               let uu____18210 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               let uu____18272 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____18210, uu____18272))
                      | uu____18299 ->
                          let uu____18300 =
                            let uu____18306 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____18306)
                             in
                          FStar_Errors.raise_error uu____18300 r
                       in
                    (match uu____18052 with
                     | (a_b,(rest_bs,f_b::[]),lift_ct) ->
                         let uu____18424 =
                           let uu____18431 =
                             let uu____18432 =
                               let uu____18433 =
                                 let uu____18440 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____18440, a)  in
                               FStar_Syntax_Syntax.NT uu____18433  in
                             [uu____18432]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____18431
                             (fun b  ->
                                let uu____18457 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____18459 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____18461 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____18463 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____18457 uu____18459 uu____18461
                                  uu____18463) r
                            in
                         (match uu____18424 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____18477 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____18477
                                then
                                  let uu____18482 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____18491 =
                                             let uu____18493 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____18493
                                              in
                                           Prims.op_Hat s uu____18491) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____18482
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____18524 =
                                           let uu____18531 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____18531, t)  in
                                         FStar_Syntax_Syntax.NT uu____18524)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____18550 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____18550
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____18556 =
                                      let uu____18558 =
                                        FStar_TypeChecker_Env.norm_eff_name
                                          env
                                          ct.FStar_Syntax_Syntax.effect_name
                                         in
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env uu____18558
                                       in
                                    effect_args_from_repr f_sort uu____18556
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____18566 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____18566)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let is =
                                  let uu____18570 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____18570
                                   in
                                let c1 =
                                  let uu____18573 =
                                    let uu____18574 =
                                      let uu____18585 =
                                        FStar_All.pipe_right is
                                          (FStar_List.map
                                             (FStar_Syntax_Subst.subst substs))
                                         in
                                      FStar_All.pipe_right uu____18585
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.as_arg)
                                       in
                                    {
                                      FStar_Syntax_Syntax.comp_univs =
                                        (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                      FStar_Syntax_Syntax.effect_name = tgt;
                                      FStar_Syntax_Syntax.result_typ = a;
                                      FStar_Syntax_Syntax.effect_args =
                                        uu____18574;
                                      FStar_Syntax_Syntax.flags =
                                        (ct.FStar_Syntax_Syntax.flags)
                                    }  in
                                  FStar_Syntax_Syntax.mk_Comp uu____18573  in
                                (let uu____18605 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "LayeredEffects")
                                    in
                                 if uu____18605
                                 then
                                   let uu____18610 =
                                     FStar_Syntax_Print.comp_to_string c1  in
                                   FStar_Util.print1 "} Lifted comp: %s\n"
                                     uu____18610
                                 else ());
                                (let uu____18615 =
                                   FStar_TypeChecker_Env.conj_guard g guard_f
                                    in
                                 (c1, uu____18615))))))))
  
let lift_tf_layered_effect_term :
  'Auu____18629 .
    'Auu____18629 ->
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
              let uu____18658 =
                let uu____18663 =
                  FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____18663
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____18658 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____18706 =
                let uu____18707 =
                  let uu____18710 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____18710
                    FStar_Syntax_Subst.compress
                   in
                uu____18707.FStar_Syntax_Syntax.n  in
              match uu____18706 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____18733::bs,uu____18735)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____18775 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____18775
                    FStar_Pervasives_Native.fst
              | uu____18881 ->
                  let uu____18882 =
                    let uu____18888 =
                      let uu____18890 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____18890
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____18888)  in
                  FStar_Errors.raise_error uu____18882
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____18917 = FStar_Syntax_Syntax.as_arg a  in
              let uu____18926 =
                let uu____18937 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____18973  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____18980 =
                  let uu____18991 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____18991]  in
                FStar_List.append uu____18937 uu____18980  in
              uu____18917 :: uu____18926  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub1  ->
      let uu____19055 =
        (let uu____19059 =
           FStar_All.pipe_right sub1.FStar_Syntax_Syntax.source
             (FStar_TypeChecker_Env.norm_eff_name env)
            in
         FStar_All.pipe_right uu____19059
           (FStar_TypeChecker_Env.is_layered_effect env))
          ||
          (FStar_All.pipe_right sub1.FStar_Syntax_Syntax.target
             (FStar_TypeChecker_Env.is_layered_effect env))
         in
      if uu____19055
      then
        let uu____19063 =
          let uu____19076 =
            FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub1.FStar_Syntax_Syntax.target uu____19076
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____19063;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub1))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____19111 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____19111 with
           | (uu____19120,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____19139 =
                 let uu____19140 =
                   let uu___2323_19141 = ct  in
                   let uu____19142 =
                     let uu____19153 =
                       let uu____19162 =
                         let uu____19163 =
                           let uu____19170 =
                             let uu____19171 =
                               let uu____19188 =
                                 let uu____19199 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____19199; wp]  in
                               (lift_t, uu____19188)  in
                             FStar_Syntax_Syntax.Tm_app uu____19171  in
                           FStar_Syntax_Syntax.mk uu____19170  in
                         uu____19163 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____19162
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____19153]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2323_19141.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub1.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2323_19141.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____19142;
                     FStar_Syntax_Syntax.flags =
                       (uu___2323_19141.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____19140  in
               (uu____19139, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____19299 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____19299 with
           | (uu____19306,lift_t) ->
               let uu____19308 =
                 let uu____19315 =
                   let uu____19316 =
                     let uu____19333 =
                       let uu____19344 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____19353 =
                         let uu____19364 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____19373 =
                           let uu____19384 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____19384]  in
                         uu____19364 :: uu____19373  in
                       uu____19344 :: uu____19353  in
                     (lift_t, uu____19333)  in
                   FStar_Syntax_Syntax.Tm_app uu____19316  in
                 FStar_Syntax_Syntax.mk uu____19315  in
               uu____19308 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____19437 =
           let uu____19450 =
             FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____19450 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____19437;
           FStar_TypeChecker_Env.mlift_term =
             (match sub1.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____19486  ->
                        fun uu____19487  -> fun e  -> FStar_Util.return_all e))
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
        let uu____19517 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____19517 with
        | (uu____19522,t) ->
            let err n1 =
              let uu____19532 =
                let uu____19538 =
                  let uu____19540 = FStar_Ident.string_of_lid datacon  in
                  let uu____19542 = FStar_Util.string_of_int n1  in
                  let uu____19544 = FStar_Util.string_of_int index1  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____19540 uu____19542 uu____19544
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____19538)
                 in
              let uu____19548 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____19532 uu____19548  in
            let uu____19549 =
              let uu____19550 = FStar_Syntax_Subst.compress t  in
              uu____19550.FStar_Syntax_Syntax.n  in
            (match uu____19549 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____19554) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____19609  ->
                           match uu____19609 with
                           | (uu____19617,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____19626 -> true)))
                    in
                 if (FStar_List.length bs1) <= index1
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index1  in
                    let uu____19658 =
                      FStar_Syntax_Util.mk_field_projector_name datacon
                        (FStar_Pervasives_Native.fst b) index1
                       in
                    FStar_All.pipe_right uu____19658
                      FStar_Pervasives_Native.fst)
             | uu____19669 -> err Prims.int_zero)
  