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
        (FStar_Ident.lident *
          (FStar_TypeChecker_Env.env ->
             FStar_Syntax_Syntax.comp ->
               (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
          * FStar_TypeChecker_Env.lift_comp_t))
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____1388 =
          let uu____1390 =
            FStar_TypeChecker_Env.try_lookup_effect_lid env
              FStar_Parser_Const.effect_GTot_lid
             in
          FStar_Option.isNone uu____1390  in
        if uu____1388
        then
          (l2,
            (FStar_TypeChecker_Env.identity_mlift.FStar_TypeChecker_Env.mlift_wp),
            (FStar_TypeChecker_Env.identity_mlift.FStar_TypeChecker_Env.mlift_wp))
        else
          (let unfold_first f en c =
             let uu____1442 =
               let uu____1443 =
                 FStar_All.pipe_right c
                   (FStar_TypeChecker_Env.unfold_effect_abbrev en)
                  in
               FStar_All.pipe_right uu____1443 FStar_Syntax_Syntax.mk_Comp
                in
             FStar_All.pipe_right uu____1442 (f en)  in
           let uu____1448 =
             let uu____1453 = FStar_TypeChecker_Env.norm_eff_name env l1  in
             let uu____1454 = FStar_TypeChecker_Env.norm_eff_name env l2  in
             (uu____1453, uu____1454)  in
           match uu____1448 with
           | (norm_l1,norm_l2) ->
               let uu____1475 =
                 let uu____1482 =
                   FStar_TypeChecker_Env.is_layered_effect env norm_l1  in
                 let uu____1484 =
                   FStar_TypeChecker_Env.is_layered_effect env norm_l2  in
                 (uu____1482, uu____1484)  in
               (match uu____1475 with
                | (l1_layered,l2_layered) ->
                    if
                      (l1_layered && l2_layered) ||
                        ((Prims.op_Negation l1_layered) &&
                           (Prims.op_Negation l2_layered))
                    then
                      let uu____1531 =
                        FStar_TypeChecker_Env.join env norm_l1 norm_l2  in
                      (match uu____1531 with
                       | (m,lift1,lift2) ->
                           let uu____1559 =
                             unfold_first
                               lift1.FStar_TypeChecker_Env.mlift_wp
                              in
                           let uu____1572 =
                             unfold_first
                               lift2.FStar_TypeChecker_Env.mlift_wp
                              in
                           (m, uu____1559, uu____1572))
                    else
                      (let uu____1591 =
                         if l1_layered
                         then (norm_l1, l2, false)
                         else (norm_l2, l1, true)  in
                       match uu____1591 with
                       | (norm_l,m,flip) ->
                           let uu____1636 = join_layered env norm_l m  in
                           (match uu____1636 with
                            | (m1,lift1,lift2) ->
                                if flip
                                then
                                  let uu____1695 = unfold_first lift1  in
                                  (m1, lift2, uu____1695)
                                else
                                  (let uu____1714 = unfold_first lift1  in
                                   (m1, uu____1714, lift2))))))
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____1755 = join env l1 l2  in
        match uu____1755 with | (m,uu____1775,uu____1776) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____1817 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2)
           in
        if uu____1817
        then FStar_Parser_Const.effect_Tot_lid
        else
          join_effects env c1.FStar_TypeChecker_Common.eff_name
            c2.FStar_TypeChecker_Common.eff_name
  
let (join_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____1846 =
          (FStar_Syntax_Util.is_total_comp c1) &&
            (FStar_Syntax_Util.is_total_comp c2)
           in
        if uu____1846
        then FStar_Parser_Const.effect_Tot_lid
        else
          (let uu____1851 =
             let uu____1853 =
               FStar_TypeChecker_Env.try_lookup_effect_lid env
                 FStar_Parser_Const.effect_GTot_lid
                in
             FStar_Option.isNone uu____1853  in
           if uu____1851
           then FStar_All.pipe_right c2 FStar_Syntax_Util.comp_effect_name
           else
             (let uu____1861 =
                FStar_All.pipe_right c1 FStar_Syntax_Util.comp_effect_name
                 in
              let uu____1864 =
                FStar_All.pipe_right c2 FStar_Syntax_Util.comp_effect_name
                 in
              join_effects env uu____1861 uu____1864))
  
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
            let uu____1915 =
              let uu____1920 = FStar_TypeChecker_Env.comp_to_comp_typ env c1
                 in
              let uu____1921 = FStar_TypeChecker_Env.comp_to_comp_typ env c2
                 in
              (uu____1920, uu____1921)  in
            match uu____1915 with
            | (c11,c21) ->
                let uu____1932 =
                  join env c11.FStar_Syntax_Syntax.effect_name
                    c21.FStar_Syntax_Syntax.effect_name
                   in
                (match uu____1932 with
                 | (m,lift1,lift2) ->
                     let uu____1986 = lift_comp env c11 lift1  in
                     (match uu____1986 with
                      | (c12,g1) ->
                          let uu____2001 =
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
                               let uu____2040 = lift_comp env_x c21 lift2  in
                               match uu____2040 with
                               | (c22,g2) ->
                                   let uu____2051 =
                                     FStar_TypeChecker_Env.close_guard env
                                       [x_a] g2
                                      in
                                   (c22, uu____2051))
                             in
                          (match uu____2001 with
                           | (c22,g2) ->
                               let uu____2074 =
                                 FStar_TypeChecker_Env.conj_guard g1 g2  in
                               (m, c12, c22, uu____2074))))
  
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
            let uu____2135 =
              let uu____2136 =
                let uu____2147 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____2147]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____2136;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____2135
  
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
          let uu____2231 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____2231
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2243 =
      let uu____2244 = FStar_Syntax_Subst.compress t  in
      uu____2244.FStar_Syntax_Syntax.n  in
    match uu____2243 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2248 -> true
    | uu____2264 -> false
  
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
              let uu____2334 =
                let uu____2336 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____2336  in
              if uu____2334
              then f
              else (let uu____2343 = reason1 ()  in label uu____2343 r f)
  
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
            let uu___303_2364 = g  in
            let uu____2365 =
              let uu____2366 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____2366  in
            {
              FStar_TypeChecker_Common.guard_f = uu____2365;
              FStar_TypeChecker_Common.deferred =
                (uu___303_2364.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___303_2364.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___303_2364.FStar_TypeChecker_Common.implicits)
            }
  
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2387 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____2387
        then c
        else
          (let uu____2392 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____2392
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close1 =
                  let uu____2434 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator
                     in
                  FStar_All.pipe_right uu____2434 FStar_Util.must  in
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____2462 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____2462]  in
                       let us =
                         let uu____2484 =
                           let uu____2487 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____2487]  in
                         u_res :: uu____2484  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____2493 =
                         let uu____2498 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md close1
                            in
                         let uu____2499 =
                           let uu____2500 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____2509 =
                             let uu____2520 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____2529 =
                               let uu____2540 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____2540]  in
                             uu____2520 :: uu____2529  in
                           uu____2500 :: uu____2509  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2498 uu____2499
                          in
                       uu____2493 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____2582 = destruct_wp_comp c1  in
              match uu____2582 with
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
                let uu____2622 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____2622
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
                  let uu____2672 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs)
                     in
                  FStar_All.pipe_right uu____2672
                    (close_guard_implicits env false bs)))
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_2685  ->
            match uu___0_2685 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____2688 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____2713 =
            let uu____2716 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____2716 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____2713
            (fun c  ->
               (let uu____2772 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____2772) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____2776 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____2776)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____2787 = FStar_Syntax_Util.head_and_args' e  in
                match uu____2787 with
                | (head1,uu____2804) ->
                    let uu____2825 =
                      let uu____2826 = FStar_Syntax_Util.un_uinst head1  in
                      uu____2826.FStar_Syntax_Syntax.n  in
                    (match uu____2825 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2831 =
                           let uu____2833 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____2833
                            in
                         Prims.op_Negation uu____2831
                     | uu____2834 -> true)))
              &&
              (let uu____2837 = should_not_inline_lc lc  in
               Prims.op_Negation uu____2837)
  
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
            let uu____2865 =
              let uu____2867 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____2867  in
            if uu____2865
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____2874 = FStar_Syntax_Util.is_unit t  in
               if uu____2874
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
                    let uu____2883 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____2883
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____2888 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____2888 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let ret_wp =
                             FStar_All.pipe_right m
                               FStar_Syntax_Util.get_return_vc_combinator
                              in
                           let uu____2899 =
                             let uu____2900 =
                               let uu____2905 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m ret_wp
                                  in
                               let uu____2906 =
                                 let uu____2907 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____2916 =
                                   let uu____2927 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____2927]  in
                                 uu____2907 :: uu____2916  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____2905
                                 uu____2906
                                in
                             uu____2900 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____2899)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____2961 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____2961
           then
             let uu____2966 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____2968 = FStar_Syntax_Print.term_to_string v1  in
             let uu____2970 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____2966 uu____2968 uu____2970
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
                (let uu____3028 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____3028
                 then
                   let uu____3033 =
                     let uu____3035 = FStar_Syntax_Syntax.mk_Comp ct1  in
                     FStar_Syntax_Print.comp_to_string uu____3035  in
                   let uu____3036 =
                     let uu____3038 = FStar_Syntax_Syntax.mk_Comp ct2  in
                     FStar_Syntax_Print.comp_to_string uu____3038  in
                   FStar_Util.print2 "Binding c1:%s and c2:%s {\n" uu____3033
                     uu____3036
                 else ());
                (let ed = FStar_TypeChecker_Env.get_effect_decl env m  in
                 let uu____3043 =
                   let uu____3054 =
                     FStar_List.hd ct1.FStar_Syntax_Syntax.comp_univs  in
                   let uu____3055 =
                     FStar_List.map FStar_Pervasives_Native.fst
                       ct1.FStar_Syntax_Syntax.effect_args
                      in
                   (uu____3054, (ct1.FStar_Syntax_Syntax.result_typ),
                     uu____3055)
                    in
                 match uu____3043 with
                 | (u1,t1,is1) ->
                     let uu____3089 =
                       let uu____3100 =
                         FStar_List.hd ct2.FStar_Syntax_Syntax.comp_univs  in
                       let uu____3101 =
                         FStar_List.map FStar_Pervasives_Native.fst
                           ct2.FStar_Syntax_Syntax.effect_args
                          in
                       (uu____3100, (ct2.FStar_Syntax_Syntax.result_typ),
                         uu____3101)
                        in
                     (match uu____3089 with
                      | (u2,t2,is2) ->
                          let uu____3135 =
                            let uu____3140 =
                              FStar_All.pipe_right ed
                                FStar_Syntax_Util.get_bind_vc_combinator
                               in
                            FStar_TypeChecker_Env.inst_tscheme_with
                              uu____3140 [u1; u2]
                             in
                          (match uu____3135 with
                           | (uu____3145,bind_t) ->
                               let bind_t_shape_error s =
                                 let uu____3160 =
                                   let uu____3162 =
                                     FStar_Syntax_Print.term_to_string bind_t
                                      in
                                   FStar_Util.format2
                                     "bind %s does not have proper shape (reason:%s)"
                                     uu____3162 s
                                    in
                                 (FStar_Errors.Fatal_UnexpectedEffect,
                                   uu____3160)
                                  in
                               let uu____3166 =
                                 let uu____3211 =
                                   let uu____3212 =
                                     FStar_Syntax_Subst.compress bind_t  in
                                   uu____3212.FStar_Syntax_Syntax.n  in
                                 match uu____3211 with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (4))
                                     ->
                                     let uu____3288 =
                                       FStar_Syntax_Subst.open_comp bs c  in
                                     (match uu____3288 with
                                      | (a_b::b_b::bs1,c1) ->
                                          let uu____3373 =
                                            let uu____3400 =
                                              FStar_List.splitAt
                                                ((FStar_List.length bs1) -
                                                   (Prims.of_int (2))) bs1
                                               in
                                            FStar_All.pipe_right uu____3400
                                              (fun uu____3485  ->
                                                 match uu____3485 with
                                                 | (l1,l2) ->
                                                     let uu____3566 =
                                                       FStar_List.hd l2  in
                                                     let uu____3579 =
                                                       let uu____3586 =
                                                         FStar_List.tl l2  in
                                                       FStar_List.hd
                                                         uu____3586
                                                        in
                                                     (l1, uu____3566,
                                                       uu____3579))
                                             in
                                          (match uu____3373 with
                                           | (rest_bs,f_b,g_b) ->
                                               let uu____3714 =
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                   c1
                                                  in
                                               (a_b, b_b, rest_bs, f_b, g_b,
                                                 uu____3714)))
                                 | uu____3747 ->
                                     let uu____3748 =
                                       bind_t_shape_error
                                         "Either not an arrow or not enough binders"
                                        in
                                     FStar_Errors.raise_error uu____3748 r1
                                  in
                               (match uu____3166 with
                                | (a_b,b_b,rest_bs,f_b,g_b,bind_ct) ->
                                    let uu____3873 =
                                      let uu____3880 =
                                        let uu____3881 =
                                          let uu____3882 =
                                            let uu____3889 =
                                              FStar_All.pipe_right a_b
                                                FStar_Pervasives_Native.fst
                                               in
                                            (uu____3889, t1)  in
                                          FStar_Syntax_Syntax.NT uu____3882
                                           in
                                        let uu____3900 =
                                          let uu____3903 =
                                            let uu____3904 =
                                              let uu____3911 =
                                                FStar_All.pipe_right b_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____3911, t2)  in
                                            FStar_Syntax_Syntax.NT uu____3904
                                             in
                                          [uu____3903]  in
                                        uu____3881 :: uu____3900  in
                                      FStar_TypeChecker_Env.uvars_for_binders
                                        env rest_bs uu____3880
                                        (fun b1  ->
                                           let uu____3926 =
                                             FStar_Syntax_Print.binder_to_string
                                               b1
                                              in
                                           let uu____3928 =
                                             FStar_Range.string_of_range r1
                                              in
                                           FStar_Util.format3
                                             "implicit var for binder %s of %s:bind at %s"
                                             uu____3926
                                             (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                             uu____3928) r1
                                       in
                                    (match uu____3873 with
                                     | (rest_bs_uvars,g_uvars) ->
                                         let subst1 =
                                           FStar_List.map2
                                             (fun b1  ->
                                                fun t  ->
                                                  let uu____3965 =
                                                    let uu____3972 =
                                                      FStar_All.pipe_right b1
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    (uu____3972, t)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____3965) (a_b :: b_b
                                             :: rest_bs) (t1 :: t2 ::
                                             rest_bs_uvars)
                                            in
                                         let f_guard =
                                           let f_sort_is =
                                             let uu____3999 =
                                               let uu____4000 =
                                                 let uu____4003 =
                                                   let uu____4004 =
                                                     FStar_All.pipe_right f_b
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   uu____4004.FStar_Syntax_Syntax.sort
                                                    in
                                                 FStar_Syntax_Subst.compress
                                                   uu____4003
                                                  in
                                               uu____4000.FStar_Syntax_Syntax.n
                                                in
                                             match uu____3999 with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____4015,uu____4016::is)
                                                 ->
                                                 let uu____4058 =
                                                   FStar_All.pipe_right is
                                                     (FStar_List.map
                                                        FStar_Pervasives_Native.fst)
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____4058
                                                   (FStar_List.map
                                                      (FStar_Syntax_Subst.subst
                                                         subst1))
                                             | uu____4091 ->
                                                 let uu____4092 =
                                                   bind_t_shape_error
                                                     "f's type is not a repr type"
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____4092 r1
                                              in
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun i1  ->
                                                  fun f_i1  ->
                                                    let uu____4108 =
                                                      FStar_TypeChecker_Rel.teq
                                                        env i1 f_i1
                                                       in
                                                    FStar_TypeChecker_Env.conj_guard
                                                      g uu____4108)
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
                                             let uu____4127 =
                                               let uu____4128 =
                                                 let uu____4131 =
                                                   let uu____4132 =
                                                     FStar_All.pipe_right g_b
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   uu____4132.FStar_Syntax_Syntax.sort
                                                    in
                                                 FStar_Syntax_Subst.compress
                                                   uu____4131
                                                  in
                                               uu____4128.FStar_Syntax_Syntax.n
                                                in
                                             match uu____4127 with
                                             | FStar_Syntax_Syntax.Tm_arrow
                                                 (bs,c) ->
                                                 let uu____4165 =
                                                   FStar_Syntax_Subst.open_comp
                                                     bs c
                                                    in
                                                 (match uu____4165 with
                                                  | (bs1,c1) ->
                                                      let bs_subst =
                                                        let uu____4175 =
                                                          let uu____4182 =
                                                            let uu____4183 =
                                                              FStar_List.hd
                                                                bs1
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____4183
                                                              FStar_Pervasives_Native.fst
                                                             in
                                                          let uu____4204 =
                                                            let uu____4207 =
                                                              FStar_All.pipe_right
                                                                x_a
                                                                FStar_Pervasives_Native.fst
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____4207
                                                              FStar_Syntax_Syntax.bv_to_name
                                                             in
                                                          (uu____4182,
                                                            uu____4204)
                                                           in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____4175
                                                         in
                                                      let c2 =
                                                        FStar_Syntax_Subst.subst_comp
                                                          [bs_subst] c1
                                                         in
                                                      let uu____4221 =
                                                        let uu____4222 =
                                                          FStar_Syntax_Subst.compress
                                                            (FStar_Syntax_Util.comp_result
                                                               c2)
                                                           in
                                                        uu____4222.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____4221 with
                                                       | FStar_Syntax_Syntax.Tm_app
                                                           (uu____4227,uu____4228::is)
                                                           ->
                                                           let uu____4270 =
                                                             FStar_All.pipe_right
                                                               is
                                                               (FStar_List.map
                                                                  FStar_Pervasives_Native.fst)
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____4270
                                                             (FStar_List.map
                                                                (FStar_Syntax_Subst.subst
                                                                   subst1))
                                                       | uu____4303 ->
                                                           let uu____4304 =
                                                             bind_t_shape_error
                                                               "g's type is not a repr type"
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4304 r1))
                                             | uu____4313 ->
                                                 let uu____4314 =
                                                   bind_t_shape_error
                                                     "g's type is not an arrow"
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____4314 r1
                                              in
                                           let env_g =
                                             FStar_TypeChecker_Env.push_binders
                                               env [x_a]
                                              in
                                           let uu____4336 =
                                             FStar_List.fold_left2
                                               (fun g  ->
                                                  fun i1  ->
                                                    fun g_i1  ->
                                                      let uu____4344 =
                                                        FStar_TypeChecker_Rel.teq
                                                          env_g i1 g_i1
                                                         in
                                                      FStar_TypeChecker_Env.conj_guard
                                                        g uu____4344)
                                               FStar_TypeChecker_Env.trivial_guard
                                               is2 g_sort_is
                                              in
                                           FStar_All.pipe_right uu____4336
                                             (FStar_TypeChecker_Env.close_guard
                                                env [x_a])
                                            in
                                         let is =
                                           let uu____4360 =
                                             let uu____4361 =
                                               FStar_Syntax_Subst.compress
                                                 bind_ct.FStar_Syntax_Syntax.result_typ
                                                in
                                             uu____4361.FStar_Syntax_Syntax.n
                                              in
                                           match uu____4360 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____4366,uu____4367::is) ->
                                               let uu____4409 =
                                                 FStar_All.pipe_right is
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_All.pipe_right
                                                 uu____4409
                                                 (FStar_List.map
                                                    (FStar_Syntax_Subst.subst
                                                       subst1))
                                           | uu____4442 ->
                                               let uu____4443 =
                                                 bind_t_shape_error
                                                   "return type is not a repr type"
                                                  in
                                               FStar_Errors.raise_error
                                                 uu____4443 r1
                                            in
                                         let c =
                                           let uu____4453 =
                                             let uu____4454 =
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
                                                 = uu____4454;
                                               FStar_Syntax_Syntax.flags =
                                                 flags
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____4453
                                            in
                                         ((let uu____4474 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env)
                                               (FStar_Options.Other
                                                  "LayeredEffects")
                                              in
                                           if uu____4474
                                           then
                                             let uu____4479 =
                                               FStar_Syntax_Print.comp_to_string
                                                 c
                                                in
                                             FStar_Util.print1
                                               "} c after bind: %s\n"
                                               uu____4479
                                           else ());
                                          (let uu____4484 =
                                             FStar_TypeChecker_Env.conj_guards
                                               [g_uvars; f_guard; g_guard]
                                              in
                                           (c, uu____4484))))))))
  
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
                let uu____4529 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____4555 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____4555 with
                  | (a,kwp) ->
                      let uu____4586 = destruct_wp_comp ct1  in
                      let uu____4593 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____4586, uu____4593)
                   in
                match uu____4529 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____4646 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____4646]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____4666 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____4666]
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
                      let uu____4713 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____4722 =
                        let uu____4733 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____4742 =
                          let uu____4753 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____4762 =
                            let uu____4773 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____4782 =
                              let uu____4793 =
                                let uu____4802 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____4802  in
                              [uu____4793]  in
                            uu____4773 :: uu____4782  in
                          uu____4753 :: uu____4762  in
                        uu____4733 :: uu____4742  in
                      uu____4713 :: uu____4722  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____4855 =
                        let uu____4860 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_t1; u_t2] env md bind_wp
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____4860 wp_args  in
                      uu____4855 FStar_Pervasives_Native.None
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
              let uu____4908 = lift_comps env c1 c2 b true  in
              match uu____4908 with
              | (m,c11,c21,g_lift) ->
                  let uu____4926 =
                    let uu____4931 = FStar_Syntax_Util.comp_to_comp_typ c11
                       in
                    let uu____4932 = FStar_Syntax_Util.comp_to_comp_typ c21
                       in
                    (uu____4931, uu____4932)  in
                  (match uu____4926 with
                   | (ct1,ct2) ->
                       let uu____4939 =
                         let uu____4944 =
                           FStar_TypeChecker_Env.is_layered_effect env m  in
                         if uu____4944
                         then mk_layered_bind env m ct1 b ct2 flags r1
                         else
                           (let uu____4953 =
                              mk_non_layered_bind env m ct1 b ct2 flags r1
                               in
                            (uu____4953, FStar_TypeChecker_Env.trivial_guard))
                          in
                       (match uu____4939 with
                        | (c,g_bind) ->
                            let uu____4960 =
                              FStar_TypeChecker_Env.conj_guard g_lift g_bind
                               in
                            (c, uu____4960)))
  
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
            let uu____4996 =
              let uu____4997 =
                let uu____5008 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____5008]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____4997;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4996  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____5053 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_5059  ->
              match uu___1_5059 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5062 -> false))
       in
    if uu____5053
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_5074  ->
              match uu___2_5074 with
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
        let uu____5102 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5102
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____5113 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____5113  in
           let pure_assume_wp1 =
             let uu____5118 = FStar_TypeChecker_Env.get_range env  in
             let uu____5119 =
               let uu____5124 =
                 let uu____5125 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____5125]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____5124  in
             uu____5119 FStar_Pervasives_Native.None uu____5118  in
           let uu____5158 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____5158)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5186 =
          let uu____5187 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5187 with
          | (c,g_c) ->
              let uu____5198 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5198
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5212 = weaken_comp env c f1  in
                     (match uu____5212 with
                      | (c1,g_w) ->
                          let uu____5223 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____5223)))
           in
        let uu____5224 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5224 weaken
  
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
              (let uu____5279 =
                 let uu____5281 =
                   FStar_TypeChecker_Env.try_lookup_effect_lid env
                     FStar_Parser_Const.effect_GTot_lid
                    in
                 FStar_Option.isNone uu____5281  in
               if uu____5279
               then (c, FStar_TypeChecker_Env.trivial_guard)
               else
                 (let r = FStar_TypeChecker_Env.get_range env  in
                  let pure_assert_wp =
                    let uu____5293 =
                      FStar_Syntax_Syntax.lid_as_fv
                        FStar_Parser_Const.pure_assert_wp_lid
                        (FStar_Syntax_Syntax.Delta_constant_at_level
                           Prims.int_one) FStar_Pervasives_Native.None
                       in
                    FStar_Syntax_Syntax.fv_to_tm uu____5293  in
                  let pure_assert_wp1 =
                    let uu____5298 =
                      let uu____5303 =
                        let uu____5304 =
                          let uu____5313 = label_opt env reason r f  in
                          FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                            uu____5313
                           in
                        [uu____5304]  in
                      FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____5303
                       in
                    uu____5298 FStar_Pervasives_Native.None r  in
                  bind_pure_wp_with env pure_assert_wp1 c flags))
  
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
            let uu____5383 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____5383
            then (lc, g0)
            else
              (let flags =
                 let uu____5395 =
                   let uu____5403 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____5403
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5395 with
                 | (maybe_trivial_post,flags) ->
                     let uu____5433 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_5441  ->
                               match uu___3_5441 with
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
                               | uu____5444 -> []))
                        in
                     FStar_List.append flags uu____5433
                  in
               let strengthen uu____5454 =
                 let uu____5455 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____5455 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____5474 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____5474 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____5481 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____5481
                              then
                                let uu____5485 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____5487 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____5485 uu____5487
                              else ());
                             (let uu____5492 =
                                strengthen_comp env reason c f flags  in
                              match uu____5492 with
                              | (c1,g_s) ->
                                  let uu____5503 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____5503))))
                  in
               let uu____5504 =
                 let uu____5505 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____5505
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____5504,
                 (let uu___620_5507 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___620_5507.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___620_5507.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___620_5507.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_5516  ->
            match uu___4_5516 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____5520 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____5549 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____5549
          then e
          else
            (let uu____5556 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____5559 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____5559)
                in
             if uu____5556
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
                | uu____5629 -> false  in
              if is_unit1
              then
                let uu____5636 =
                  let uu____5638 =
                    let uu____5639 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____5639
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____5638
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____5636
                 then
                   let uu____5648 =
                     FStar_Syntax_Subst.open_term
                       [(b, FStar_Pervasives_Native.None)] phi
                      in
                   match uu____5648 with
                   | (b1::[],phi1) ->
                       let phi2 =
                         let uu____5692 =
                           let uu____5695 =
                             let uu____5696 =
                               let uu____5703 =
                                 FStar_All.pipe_right b1
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____5703, FStar_Syntax_Syntax.unit_const)
                                in
                             FStar_Syntax_Syntax.NT uu____5696  in
                           [uu____5695]  in
                         FStar_Syntax_Subst.subst uu____5692 phi1  in
                       weaken_comp env c phi2
                 else
                   (let uu____5716 = close_wp_comp env [x] c  in
                    (uu____5716, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____5719 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
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
          fun uu____5747  ->
            match uu____5747 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____5767 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____5767 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let bind_flags =
                  let uu____5779 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____5779
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____5789 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____5789
                       then
                         let uu____5794 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____5794
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5801 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____5801
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5810 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____5810
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____5817 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____5817
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let uu____5824 = FStar_TypeChecker_Common.lcomp_comp lc11  in
                (match uu____5824 with
                 | (c1,g_c1) ->
                     let uu____5831 =
                       FStar_TypeChecker_Common.lcomp_comp lc21  in
                     (match uu____5831 with
                      | (c2,g_c2) ->
                          let joined_eff = join_comp env c1 c2  in
                          let bind_it uu____5848 =
                            let uu____5849 =
                              env.FStar_TypeChecker_Env.lax &&
                                (FStar_Options.ml_ish ())
                               in
                            if uu____5849
                            then
                              let u_t =
                                env.FStar_TypeChecker_Env.universe_of env
                                  lc21.FStar_TypeChecker_Common.res_typ
                                 in
                              let uu____5857 =
                                lax_mk_tot_or_comp_l joined_eff u_t
                                  lc21.FStar_TypeChecker_Common.res_typ []
                                 in
                              let uu____5858 =
                                FStar_TypeChecker_Env.conj_guard g_c1 g_c2
                                 in
                              (uu____5857, uu____5858)
                            else
                              (debug1
                                 (fun uu____5870  ->
                                    let uu____5871 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____5873 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____5878 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____5871 uu____5873 uu____5878);
                               (let aux uu____5896 =
                                  let uu____5897 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____5897
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____5928
                                        ->
                                        let uu____5929 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____5929
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____5961 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____5961
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____6008 =
                                  let aux_with_trivial_guard uu____6038 =
                                    let uu____6039 = aux ()  in
                                    match uu____6039 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c,
                                            FStar_TypeChecker_Env.trivial_guard,
                                            reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____6097 =
                                    let uu____6099 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____6099  in
                                  if uu____6097
                                  then
                                    let uu____6115 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____6115
                                     then
                                       FStar_Util.Inl
                                         (c2,
                                           FStar_TypeChecker_Env.trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____6142 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____6142))
                                  else
                                    (let uu____6159 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____6159
                                     then
                                       let close1 x reason c =
                                         let x1 =
                                           let uu___719_6205 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___719_6205.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___719_6205.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           }  in
                                         let uu____6206 =
                                           maybe_capture_unit_refinement env
                                             x1.FStar_Syntax_Syntax.sort x1 c
                                            in
                                         match uu____6206 with
                                         | (c3,g_c) ->
                                             FStar_Util.Inl (c3, g_c, reason)
                                          in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some
                                          e,FStar_Pervasives_Native.Some x)
                                           ->
                                           let uu____6264 =
                                             FStar_All.pipe_right c2
                                               (FStar_Syntax_Subst.subst_comp
                                                  [FStar_Syntax_Syntax.NT
                                                     (x, e)])
                                              in
                                           FStar_All.pipe_right uu____6264
                                             (close1 x "c1 Tot")
                                       | (uu____6280,FStar_Pervasives_Native.Some
                                          x) ->
                                           FStar_All.pipe_right c2
                                             (close1 x "c1 Tot only close")
                                       | (uu____6305,uu____6306) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____6321 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____6321
                                        then
                                          let uu____6336 =
                                            let uu____6344 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____6344,
                                              FStar_TypeChecker_Env.trivial_guard,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____6336
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____6357 = try_simplify ()  in
                                match uu____6357 with
                                | FStar_Util.Inl (c,g_c,reason) ->
                                    (debug1
                                       (fun uu____6392  ->
                                          let uu____6393 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____6393);
                                     (let uu____6396 =
                                        let uu____6397 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_c1 g_c2
                                           in
                                        FStar_TypeChecker_Env.conj_guard g_c
                                          uu____6397
                                         in
                                      (c, uu____6396)))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____6411  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 =
                                        let uu____6437 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____6437 with
                                        | (c,g_bind) ->
                                            let uu____6448 =
                                              let uu____6449 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g_c1 g_c2
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                uu____6449 g_bind
                                               in
                                            (c, uu____6448)
                                         in
                                      let mk_seq c11 b1 c21 =
                                        let uu____6474 =
                                          let uu____6479 =
                                            FStar_TypeChecker_Env.comp_to_comp_typ
                                              env c11
                                             in
                                          let uu____6480 =
                                            FStar_TypeChecker_Env.comp_to_comp_typ
                                              env c21
                                             in
                                          (uu____6479, uu____6480)  in
                                        match uu____6474 with
                                        | (c12,c22) ->
                                            let uu____6487 =
                                              join env
                                                c12.FStar_Syntax_Syntax.effect_name
                                                c22.FStar_Syntax_Syntax.effect_name
                                               in
                                            (match uu____6487 with
                                             | (m,uu____6511,lift2) ->
                                                 let uu____6537 =
                                                   lift_comp env c22 lift2
                                                    in
                                                 (match uu____6537 with
                                                  | (c23,g2) ->
                                                      let uu____6548 =
                                                        destruct_wp_comp c12
                                                         in
                                                      (match uu____6548 with
                                                       | (u1,t1,wp1) ->
                                                           let md_pure_or_ghost
                                                             =
                                                             FStar_TypeChecker_Env.get_effect_decl
                                                               env
                                                               c12.FStar_Syntax_Syntax.effect_name
                                                              in
                                                           let trivial =
                                                             let uu____6564 =
                                                               FStar_All.pipe_right
                                                                 md_pure_or_ghost
                                                                 FStar_Syntax_Util.get_wp_trivial_combinator
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____6564
                                                               FStar_Util.must
                                                              in
                                                           let vc1 =
                                                             let uu____6574 =
                                                               let uu____6579
                                                                 =
                                                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                                                   [u1] env
                                                                   md_pure_or_ghost
                                                                   trivial
                                                                  in
                                                               let uu____6580
                                                                 =
                                                                 let uu____6581
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    t1
                                                                    in
                                                                 let uu____6590
                                                                   =
                                                                   let uu____6601
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp1  in
                                                                   [uu____6601]
                                                                    in
                                                                 uu____6581
                                                                   ::
                                                                   uu____6590
                                                                  in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____6579
                                                                 uu____6580
                                                                in
                                                             uu____6574
                                                               FStar_Pervasives_Native.None
                                                               r1
                                                              in
                                                           let uu____6634 =
                                                             strengthen_comp
                                                               env
                                                               FStar_Pervasives_Native.None
                                                               c23 vc1
                                                               bind_flags
                                                              in
                                                           (match uu____6634
                                                            with
                                                            | (c,g_s) ->
                                                                let uu____6649
                                                                  =
                                                                  FStar_TypeChecker_Env.conj_guards
                                                                    [g_c1;
                                                                    g_c2;
                                                                    g2;
                                                                    g_s]
                                                                   in
                                                                (c,
                                                                  uu____6649)))))
                                         in
                                      let uu____6650 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____6666 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____6666, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____6650 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____6682 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____6682
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____6691 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____6691
                                             then
                                               (debug1
                                                  (fun uu____6705  ->
                                                     let uu____6706 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____6708 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____6706 uu____6708);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 mk_bind1 c1 b c21))
                                             else
                                               (let uu____6716 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____6719 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____6719)
                                                   in
                                                if uu____6716
                                                then
                                                  let e1' =
                                                    let uu____6744 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____6744
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug1
                                                     (fun uu____6756  ->
                                                        let uu____6757 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____6759 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____6757
                                                          uu____6759);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug1
                                                     (fun uu____6774  ->
                                                        let uu____6775 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____6777 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____6775
                                                          uu____6777);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____6784 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____6784
                                                       in
                                                    let uu____6785 =
                                                      let uu____6790 =
                                                        let uu____6791 =
                                                          let uu____6792 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____6792]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____6791
                                                         in
                                                      weaken_comp uu____6790
                                                        c21 x_eq_e
                                                       in
                                                    match uu____6785 with
                                                    | (c22,g_w) ->
                                                        let uu____6817 =
                                                          mk_bind1 c1 b c22
                                                           in
                                                        (match uu____6817
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____6828 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____6828))))))
                                          else mk_bind1 c1 b c2))))
                             in
                          FStar_TypeChecker_Common.mk_lcomp joined_eff
                            lc21.FStar_TypeChecker_Common.res_typ bind_flags
                            bind_it))
  
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
      | uu____6845 -> g2
  
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
            (let uu____6869 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____6869)
           in
        let flags =
          if should_return1
          then
            let uu____6877 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____6877
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____6895 =
          let uu____6896 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____6896 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____6909 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____6909
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____6917 =
                  let uu____6919 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____6919  in
                (if uu____6917
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___839_6928 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___839_6928.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___839_6928.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___839_6928.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____6929 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____6929, g_c)
                 else
                   (let uu____6932 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____6932, g_c)))
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
                   let uu____6943 =
                     let uu____6944 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____6944
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____6943
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____6947 =
                   let uu____6952 =
                     let uu____6953 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____6953
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____6952  in
                 match uu____6947 with
                 | (bind_c,g_bind) ->
                     let uu____6962 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____6963 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____6962, uu____6963))
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
            fun uu____6999  ->
              match uu____6999 with
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
                    let uu____7011 =
                      ((let uu____7015 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____7015) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____7011
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____7033 =
        let uu____7034 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____7034  in
      FStar_Syntax_Syntax.fvar uu____7033 FStar_Syntax_Syntax.delta_constant
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
                  let uu____7084 =
                    let uu____7089 =
                      let uu____7090 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____7090 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7089 [u_a]
                     in
                  match uu____7084 with
                  | (uu____7101,conjunction) ->
                      let uu____7103 =
                        let uu____7112 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____7127 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____7112, uu____7127)  in
                      (match uu____7103 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____7173 =
                               let uu____7175 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____7175 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7173)
                              in
                           let uu____7179 =
                             let uu____7224 =
                               let uu____7225 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____7225.FStar_Syntax_Syntax.n  in
                             match uu____7224 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____7274) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____7306 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____7306 with
                                  | (a_b::bs1,body1) ->
                                      let uu____7378 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____7378 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____7526 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____7526)))
                             | uu____7559 ->
                                 let uu____7560 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____7560 r
                              in
                           (match uu____7179 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____7685 =
                                  let uu____7692 =
                                    let uu____7693 =
                                      let uu____7694 =
                                        let uu____7701 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____7701, a)  in
                                      FStar_Syntax_Syntax.NT uu____7694  in
                                    [uu____7693]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____7692
                                    (fun b  ->
                                       let uu____7717 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____7719 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____7721 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____7717 uu____7719 uu____7721) r
                                   in
                                (match uu____7685 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____7759 =
                                                let uu____7766 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____7766, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____7759) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____7805 =
                                           let uu____7806 =
                                             let uu____7809 =
                                               let uu____7810 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____7810.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____7809
                                              in
                                           uu____7806.FStar_Syntax_Syntax.n
                                            in
                                         match uu____7805 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____7821,uu____7822::is) ->
                                             let uu____7864 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____7864
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____7897 ->
                                             let uu____7898 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____7898 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____7914 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____7914)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____7919 =
                                           let uu____7920 =
                                             let uu____7923 =
                                               let uu____7924 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____7924.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____7923
                                              in
                                           uu____7920.FStar_Syntax_Syntax.n
                                            in
                                         match uu____7919 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____7935,uu____7936::is) ->
                                             let uu____7978 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____7978
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8011 ->
                                             let uu____8012 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8012 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____8028 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8028)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____8033 =
                                         let uu____8034 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____8034.FStar_Syntax_Syntax.n  in
                                       match uu____8033 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8039,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8094 ->
                                           let uu____8095 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____8095 r
                                        in
                                     let uu____8104 =
                                       let uu____8105 =
                                         let uu____8106 =
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
                                             uu____8106;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____8105
                                        in
                                     let uu____8129 =
                                       let uu____8130 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8130 g_guard
                                        in
                                     (uu____8104, uu____8129))))
  
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
                fun uu____8175  ->
                  let if_then_else1 =
                    let uu____8181 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____8181 FStar_Util.must  in
                  let uu____8188 = destruct_wp_comp ct1  in
                  match uu____8188 with
                  | (uu____8199,uu____8200,wp_t) ->
                      let uu____8202 = destruct_wp_comp ct2  in
                      (match uu____8202 with
                       | (uu____8213,uu____8214,wp_e) ->
                           let wp =
                             let uu____8219 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             let uu____8220 =
                               let uu____8225 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_a] env ed if_then_else1
                                  in
                               let uu____8226 =
                                 let uu____8227 =
                                   FStar_Syntax_Syntax.as_arg a  in
                                 let uu____8236 =
                                   let uu____8247 =
                                     FStar_Syntax_Syntax.as_arg p  in
                                   let uu____8256 =
                                     let uu____8267 =
                                       FStar_Syntax_Syntax.as_arg wp_t  in
                                     let uu____8276 =
                                       let uu____8287 =
                                         FStar_Syntax_Syntax.as_arg wp_e  in
                                       [uu____8287]  in
                                     uu____8267 :: uu____8276  in
                                   uu____8247 :: uu____8256  in
                                 uu____8227 :: uu____8236  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____8225
                                 uu____8226
                                in
                             uu____8220 FStar_Pervasives_Native.None
                               uu____8219
                              in
                           let uu____8336 = mk_comp ed u_a a wp []  in
                           (uu____8336, FStar_TypeChecker_Env.trivial_guard))
  
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
               fun uu____8406  ->
                 match uu____8406 with
                 | (uu____8420,eff_label,uu____8422,uu____8423) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____8436 =
          let uu____8444 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____8482  ->
                    match uu____8482 with
                    | (uu____8497,uu____8498,flags,uu____8500) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_8517  ->
                                match uu___5_8517 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____8520 -> false))))
             in
          if uu____8444
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____8436 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____8557 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____8559 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____8559
              then
                let uu____8566 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                   in
                (uu____8566, FStar_TypeChecker_Env.trivial_guard)
              else
                (let default_case =
                   let post_k =
                     let uu____8573 =
                       let uu____8582 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____8582]  in
                     let uu____8601 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____8573 uu____8601  in
                   let kwp =
                     let uu____8607 =
                       let uu____8616 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____8616]  in
                     let uu____8635 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____8607 uu____8635  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____8642 =
                       let uu____8643 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____8643]  in
                     let uu____8662 =
                       let uu____8665 =
                         let uu____8672 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____8672
                          in
                       let uu____8673 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____8665 uu____8673  in
                     FStar_Syntax_Util.abs uu____8642 uu____8662
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
                   let uu____8697 =
                     should_not_inline_whole_match ||
                       (let uu____8700 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____8700)
                      in
                   if uu____8697 then cthen true else cthen false  in
                 let uu____8707 =
                   FStar_List.fold_right
                     (fun uu____8760  ->
                        fun uu____8761  ->
                          match (uu____8760, uu____8761) with
                          | ((g,eff_label,uu____8815,cthen),(uu____8817,celse,g_comp))
                              ->
                              let uu____8858 =
                                let uu____8863 = maybe_return eff_label cthen
                                   in
                                FStar_TypeChecker_Common.lcomp_comp
                                  uu____8863
                                 in
                              (match uu____8858 with
                               | (cthen1,gthen) ->
                                   let uu____8874 =
                                     let uu____8883 =
                                       lift_comps env cthen1 celse
                                         FStar_Pervasives_Native.None false
                                        in
                                     match uu____8883 with
                                     | (m,cthen2,celse1,g_lift) ->
                                         let md =
                                           FStar_TypeChecker_Env.get_effect_decl
                                             env m
                                            in
                                         let uu____8906 =
                                           FStar_All.pipe_right cthen2
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         let uu____8907 =
                                           FStar_All.pipe_right celse1
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         (md, uu____8906, uu____8907, g_lift)
                                      in
                                   (match uu____8874 with
                                    | (md,ct_then,ct_else,g_lift) ->
                                        let fn =
                                          let uu____8957 =
                                            FStar_All.pipe_right md
                                              FStar_Syntax_Util.is_layered
                                             in
                                          if uu____8957
                                          then mk_layered_conjunction
                                          else mk_non_layered_conjunction  in
                                        let uu____8991 =
                                          let uu____8996 =
                                            FStar_TypeChecker_Env.get_range
                                              env
                                             in
                                          fn env md u_res_t res_t g ct_then
                                            ct_else uu____8996
                                           in
                                        (match uu____8991 with
                                         | (c,g_conjunction) ->
                                             let uu____9007 =
                                               let uu____9008 =
                                                 let uu____9009 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_comp gthen
                                                    in
                                                 FStar_TypeChecker_Env.conj_guard
                                                   uu____9009 g_lift
                                                  in
                                               FStar_TypeChecker_Env.conj_guard
                                                 uu____9008 g_conjunction
                                                in
                                             ((FStar_Pervasives_Native.Some
                                                 md), c, uu____9007)))))
                     lcases
                     (FStar_Pervasives_Native.None, default_case,
                       FStar_TypeChecker_Env.trivial_guard)
                    in
                 match uu____8707 with
                 | (md,comp,g_comp) ->
                     (match lcases with
                      | [] -> (comp, g_comp)
                      | uu____9043::[] -> (comp, g_comp)
                      | uu____9086 ->
                          let uu____9103 =
                            let uu____9105 =
                              FStar_All.pipe_right md FStar_Util.must  in
                            FStar_All.pipe_right uu____9105
                              FStar_Syntax_Util.is_layered
                             in
                          if uu____9103
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
                             let uu____9118 = destruct_wp_comp comp1  in
                             match uu____9118 with
                             | (uu____9129,uu____9130,wp) ->
                                 let ite_wp =
                                   let uu____9133 =
                                     FStar_All.pipe_right md1
                                       FStar_Syntax_Util.get_wp_ite_combinator
                                      in
                                   FStar_All.pipe_right uu____9133
                                     FStar_Util.must
                                    in
                                 let wp1 =
                                   let uu____9143 =
                                     let uu____9148 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_res_t] env md1 ite_wp
                                        in
                                     let uu____9149 =
                                       let uu____9150 =
                                         FStar_Syntax_Syntax.as_arg res_t  in
                                       let uu____9159 =
                                         let uu____9170 =
                                           FStar_Syntax_Syntax.as_arg wp  in
                                         [uu____9170]  in
                                       uu____9150 :: uu____9159  in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____9148
                                       uu____9149
                                      in
                                   uu____9143 FStar_Pervasives_Native.None
                                     wp.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____9203 =
                                   mk_comp md1 u_res_t res_t wp1
                                     bind_cases_flags
                                    in
                                 (uu____9203, g_comp))))
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
          let uu____9237 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____9237 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____9253 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____9259 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____9253 uu____9259
              else
                (let uu____9268 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____9274 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____9268 uu____9274)
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
          let uu____9299 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____9299
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____9302 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____9302
        then u_res
        else
          (let is_total =
             let uu____9309 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____9309
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____9320 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____9320 with
              | FStar_Pervasives_Native.None  ->
                  let uu____9323 =
                    let uu____9329 =
                      let uu____9331 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____9331
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____9329)
                     in
                  FStar_Errors.raise_error uu____9323
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
      let uu____9355 = destruct_wp_comp ct  in
      match uu____9355 with
      | (u_t,t,wp) ->
          let vc =
            let uu____9374 = FStar_TypeChecker_Env.get_range env  in
            let uu____9375 =
              let uu____9380 =
                let uu____9381 =
                  let uu____9382 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_trivial_combinator
                     in
                  FStar_All.pipe_right uu____9382 FStar_Util.must  in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____9381
                 in
              let uu____9389 =
                let uu____9390 = FStar_Syntax_Syntax.as_arg t  in
                let uu____9399 =
                  let uu____9410 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____9410]  in
                uu____9390 :: uu____9399  in
              FStar_Syntax_Syntax.mk_Tm_app uu____9380 uu____9389  in
            uu____9375 FStar_Pervasives_Native.None uu____9374  in
          let uu____9443 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____9443)
  
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
                  let uu____9498 = FStar_TypeChecker_Env.try_lookup_lid env f
                     in
                  match uu____9498 with
                  | FStar_Pervasives_Native.Some uu____9513 ->
                      ((let uu____9531 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____9531
                        then
                          let uu____9535 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____9535
                        else ());
                       (let coercion =
                          let uu____9541 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____9541
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____9548 =
                            let uu____9549 =
                              let uu____9550 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____9550
                               in
                            (FStar_Pervasives_Native.None, uu____9549)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____9548
                           in
                        let e1 =
                          let uu____9556 =
                            let uu____9561 =
                              let uu____9562 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____9562]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____9561
                             in
                          uu____9556 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____9596 =
                          let uu____9602 =
                            let uu____9604 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____9604
                             in
                          (FStar_Errors.Warning_CoercionNotFound, uu____9602)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____9596);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____9623 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____9641 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____9652 -> false 
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
      let uu____9676 = FStar_Syntax_Util.head_and_args t2  in
      match uu____9676 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____9721 =
              let uu____9736 =
                let uu____9737 = FStar_Syntax_Subst.compress h1  in
                uu____9737.FStar_Syntax_Syntax.n  in
              (uu____9736, args)  in
            match uu____9721 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____9784,uu____9785) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____9818) -> Maybe
            | uu____9839 -> No  in
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
            (((let uu____9891 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____9891) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____9910 =
                 let uu____9911 = FStar_Syntax_Subst.compress t1  in
                 uu____9911.FStar_Syntax_Syntax.n  in
               match uu____9910 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____9916 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____9926 =
                 let uu____9927 = FStar_Syntax_Subst.compress t1  in
                 uu____9927.FStar_Syntax_Syntax.n  in
               match uu____9926 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____9932 -> false  in
             let is_type1 t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____9942 =
                 let uu____9943 = FStar_Syntax_Subst.compress t1  in
                 uu____9943.FStar_Syntax_Syntax.n  in
               match uu____9942 with
               | FStar_Syntax_Syntax.Tm_type uu____9947 -> true
               | uu____9949 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____9952 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____9952 with
             | (head1,args) ->
                 ((let uu____10002 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____10002
                   then
                     let uu____10006 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____10008 = FStar_Syntax_Print.term_to_string e
                        in
                     let uu____10010 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____10012 =
                       FStar_Syntax_Print.term_to_string exp_t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____10006 uu____10008 uu____10010 uu____10012
                   else ());
                  (let mk_erased u t =
                     let uu____10030 =
                       let uu____10033 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____10033 [u]  in
                     let uu____10034 =
                       let uu____10045 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____10045]  in
                     FStar_Syntax_Util.mk_app uu____10030 uu____10034  in
                   let uu____10070 =
                     let uu____10085 =
                       let uu____10086 = FStar_Syntax_Util.un_uinst head1  in
                       uu____10086.FStar_Syntax_Syntax.n  in
                     (uu____10085, args)  in
                   match uu____10070 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type1 exp_t)
                       ->
                       let uu____10124 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____10124 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____10164 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____10164 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____10204 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____10204 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____10244 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____10244 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____10265 ->
                       let uu____10280 =
                         let uu____10285 = check_erased env res_typ  in
                         let uu____10286 = check_erased env exp_t  in
                         (uu____10285, uu____10286)  in
                       (match uu____10280 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____10295 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____10295 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____10306 =
                                   let uu____10311 =
                                     let uu____10312 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____10312]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____10311
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____10306 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____10347 =
                              let uu____10352 =
                                let uu____10353 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____10353]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____10352
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____10347 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____10386 ->
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
        let uu____10421 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____10421 with
        | (hd1,args) ->
            let uu____10470 =
              let uu____10485 =
                let uu____10486 = FStar_Syntax_Subst.compress hd1  in
                uu____10486.FStar_Syntax_Syntax.n  in
              (uu____10485, args)  in
            (match uu____10470 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____10524 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun _10551  -> FStar_Pervasives_Native.Some _10551)
                   uu____10524
             | uu____10552 -> FStar_Pervasives_Native.None)
  
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
          (let uu____10605 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____10605
           then
             let uu____10608 = FStar_Syntax_Print.term_to_string e  in
             let uu____10610 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____10612 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____10608 uu____10610 uu____10612
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____10622 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____10622 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____10647 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____10673 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____10673, false)
             else
               (let uu____10683 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____10683, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____10696) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____10708 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____10708
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1239_10724 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1239_10724.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1239_10724.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1239_10724.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____10731 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____10731 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____10747 =
                      let uu____10748 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____10748 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____10768 =
                            let uu____10770 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____10770 = FStar_Syntax_Util.Equal  in
                          if uu____10768
                          then
                            ((let uu____10777 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____10777
                              then
                                let uu____10781 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____10783 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____10781 uu____10783
                              else ());
                             (let uu____10788 = set_result_typ1 c  in
                              (uu____10788, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____10795 ->
                                   true
                               | uu____10803 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____10812 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____10812
                                  in
                               let lc1 =
                                 let uu____10814 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____10815 =
                                   let uu____10816 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____10816)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____10814 uu____10815
                                  in
                               ((let uu____10820 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____10820
                                 then
                                   let uu____10824 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____10826 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____10828 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____10830 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____10824 uu____10826 uu____10828
                                     uu____10830
                                 else ());
                                (let uu____10835 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____10835 with
                                 | (c1,g_lc) ->
                                     let uu____10846 = set_result_typ1 c1  in
                                     let uu____10847 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____10846, uu____10847)))
                             else
                               ((let uu____10851 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____10851
                                 then
                                   let uu____10855 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____10857 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____10855 uu____10857
                                 else ());
                                (let uu____10862 = set_result_typ1 c  in
                                 (uu____10862, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1276_10866 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1276_10866.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1276_10866.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1276_10866.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____10876 =
                      let uu____10877 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____10877
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____10887 =
                           let uu____10888 = FStar_Syntax_Subst.compress f1
                              in
                           uu____10888.FStar_Syntax_Syntax.n  in
                         match uu____10887 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____10895,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____10897;
                                            FStar_Syntax_Syntax.vars =
                                              uu____10898;_},uu____10899)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1292_10925 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1292_10925.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1292_10925.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1292_10925.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____10926 ->
                             let uu____10927 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____10927 with
                              | (c,g_c) ->
                                  ((let uu____10939 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____10939
                                    then
                                      let uu____10943 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____10945 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____10947 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____10949 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____10943 uu____10945 uu____10947
                                        uu____10949
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
                                        let uu____10962 =
                                          let uu____10967 =
                                            let uu____10968 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____10968]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____10967
                                           in
                                        uu____10962
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____10995 =
                                      let uu____11000 =
                                        FStar_All.pipe_left
                                          (fun _11021  ->
                                             FStar_Pervasives_Native.Some
                                               _11021)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____11022 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____11023 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____11024 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____11000
                                        uu____11022 e uu____11023 uu____11024
                                       in
                                    match uu____10995 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1310_11032 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1310_11032.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1310_11032.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____11034 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____11034
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____11037 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____11037 with
                                         | (c2,g_lc) ->
                                             ((let uu____11049 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____11049
                                               then
                                                 let uu____11053 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____11053
                                               else ());
                                              (let uu____11058 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____11058))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_11067  ->
                              match uu___6_11067 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____11070 -> []))
                       in
                    let lc1 =
                      let uu____11072 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____11072 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1326_11074 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1326_11074.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1326_11074.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1326_11074.FStar_TypeChecker_Common.implicits)
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
        let uu____11110 =
          let uu____11113 =
            let uu____11118 =
              let uu____11119 =
                let uu____11128 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____11128  in
              [uu____11119]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____11118  in
          uu____11113 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____11110  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____11151 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____11151
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____11170 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____11186 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____11203 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____11203
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____11219)::(ens,uu____11221)::uu____11222 ->
                    let uu____11265 =
                      let uu____11268 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____11268  in
                    let uu____11269 =
                      let uu____11270 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____11270  in
                    (uu____11265, uu____11269)
                | uu____11273 ->
                    let uu____11284 =
                      let uu____11290 =
                        let uu____11292 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____11292
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____11290)
                       in
                    FStar_Errors.raise_error uu____11284
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____11312)::uu____11313 ->
                    let uu____11340 =
                      let uu____11345 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____11345
                       in
                    (match uu____11340 with
                     | (us_r,uu____11377) ->
                         let uu____11378 =
                           let uu____11383 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____11383
                            in
                         (match uu____11378 with
                          | (us_e,uu____11415) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____11418 =
                                  let uu____11419 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____11419
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____11418
                                  us_r
                                 in
                              let as_ens =
                                let uu____11421 =
                                  let uu____11422 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____11422
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____11421
                                  us_e
                                 in
                              let req =
                                let uu____11426 =
                                  let uu____11431 =
                                    let uu____11432 =
                                      let uu____11443 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____11443]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____11432
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____11431
                                   in
                                uu____11426 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____11483 =
                                  let uu____11488 =
                                    let uu____11489 =
                                      let uu____11500 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____11500]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____11489
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____11488
                                   in
                                uu____11483 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____11537 =
                                let uu____11540 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____11540  in
                              let uu____11541 =
                                let uu____11542 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____11542  in
                              (uu____11537, uu____11541)))
                | uu____11545 -> failwith "Impossible"))
  
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
        (let uu____11584 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____11584
         then
           let uu____11589 = FStar_Syntax_Print.term_to_string tm  in
           let uu____11591 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____11589
             uu____11591
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
          (let uu____11650 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____11650
           then
             let uu____11655 = FStar_Syntax_Print.term_to_string tm  in
             let uu____11657 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____11655
               uu____11657
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____11668 =
      let uu____11670 =
        let uu____11671 = FStar_Syntax_Subst.compress t  in
        uu____11671.FStar_Syntax_Syntax.n  in
      match uu____11670 with
      | FStar_Syntax_Syntax.Tm_app uu____11675 -> false
      | uu____11693 -> true  in
    if uu____11668
    then t
    else
      (let uu____11698 = FStar_Syntax_Util.head_and_args t  in
       match uu____11698 with
       | (head1,args) ->
           let uu____11741 =
             let uu____11743 =
               let uu____11744 = FStar_Syntax_Subst.compress head1  in
               uu____11744.FStar_Syntax_Syntax.n  in
             match uu____11743 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____11749 -> false  in
           if uu____11741
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____11781 ->
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
          ((let uu____11828 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____11828
            then
              let uu____11831 = FStar_Syntax_Print.term_to_string e  in
              let uu____11833 = FStar_Syntax_Print.term_to_string t  in
              let uu____11835 =
                let uu____11837 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____11837
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____11831 uu____11833 uu____11835
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____11850 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____11850 with
              | (formals,uu____11866) ->
                  let n_implicits =
                    let uu____11888 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____11966  ->
                              match uu____11966 with
                              | (uu____11974,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____11981 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____11981 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____11888 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____12106 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____12106 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____12120 =
                      let uu____12126 =
                        let uu____12128 = FStar_Util.string_of_int n_expected
                           in
                        let uu____12130 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____12132 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____12128 uu____12130 uu____12132
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____12126)
                       in
                    let uu____12136 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____12120 uu____12136
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_12154 =
              match uu___7_12154 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____12197 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____12197 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _12328,uu____12315)
                           when _12328 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____12361,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____12363))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____12397 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____12397 with
                            | (v1,uu____12438,g) ->
                                ((let uu____12453 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____12453
                                  then
                                    let uu____12456 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____12456
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____12466 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____12466 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____12559 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____12559))))
                       | (uu____12586,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____12623 =
                             let uu____12636 =
                               let uu____12643 =
                                 let uu____12648 = FStar_Dyn.mkdyn env  in
                                 (uu____12648, tau)  in
                               FStar_Pervasives_Native.Some uu____12643  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____12636
                              in
                           (match uu____12623 with
                            | (v1,uu____12681,g) ->
                                ((let uu____12696 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____12696
                                  then
                                    let uu____12699 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____12699
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____12709 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____12709 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____12802 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____12802))))
                       | (uu____12829,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____12877 =
                       let uu____12904 = inst_n_binders t1  in
                       aux [] uu____12904 bs1  in
                     (match uu____12877 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____12976) -> (e, torig, guard)
                           | (uu____13007,[]) when
                               let uu____13038 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____13038 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____13040 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____13068 ->
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
            | uu____13081 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____13093 =
      let uu____13097 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____13097
        (FStar_List.map
           (fun u  ->
              let uu____13109 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____13109 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____13093 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____13137 = FStar_Util.set_is_empty x  in
      if uu____13137
      then []
      else
        (let s =
           let uu____13155 =
             let uu____13158 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____13158  in
           FStar_All.pipe_right uu____13155 FStar_Util.set_elements  in
         (let uu____13174 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____13174
          then
            let uu____13179 =
              let uu____13181 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____13181  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____13179
          else ());
         (let r =
            let uu____13190 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____13190  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____13229 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____13229
                     then
                       let uu____13234 =
                         let uu____13236 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____13236
                          in
                       let uu____13240 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____13242 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____13234 uu____13240 uu____13242
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
        let uu____13272 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____13272 FStar_Util.set_elements  in
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
        | ([],uu____13311) -> generalized_univ_names
        | (uu____13318,[]) -> explicit_univ_names
        | uu____13325 ->
            let uu____13334 =
              let uu____13340 =
                let uu____13342 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____13342
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____13340)
               in
            FStar_Errors.raise_error uu____13334 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____13364 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____13364
       then
         let uu____13369 = FStar_Syntax_Print.term_to_string t  in
         let uu____13371 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____13369 uu____13371
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____13380 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____13380
        then
          let uu____13385 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____13385
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____13394 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____13394
         then
           let uu____13399 = FStar_Syntax_Print.term_to_string t  in
           let uu____13401 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____13399 uu____13401
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
        let uu____13485 =
          let uu____13487 =
            FStar_Util.for_all
              (fun uu____13501  ->
                 match uu____13501 with
                 | (uu____13511,uu____13512,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____13487  in
        if uu____13485
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____13564 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____13564
              then
                let uu____13567 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____13567
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____13574 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____13574
               then
                 let uu____13577 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____13577
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____13595 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____13595 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____13629 =
             match uu____13629 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____13666 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____13666
                   then
                     let uu____13671 =
                       let uu____13673 =
                         let uu____13677 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____13677
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____13673
                         (FStar_String.concat ", ")
                        in
                     let uu____13725 =
                       let uu____13727 =
                         let uu____13731 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____13731
                           (FStar_List.map
                              (fun u  ->
                                 let uu____13744 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____13746 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____13744
                                   uu____13746))
                          in
                       FStar_All.pipe_right uu____13727
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____13671
                       uu____13725
                   else ());
                  (let univs2 =
                     let uu____13760 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____13772 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____13772) univs1
                       uu____13760
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____13779 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____13779
                    then
                      let uu____13784 =
                        let uu____13786 =
                          let uu____13790 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____13790
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____13786
                          (FStar_String.concat ", ")
                         in
                      let uu____13838 =
                        let uu____13840 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____13854 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____13856 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____13854
                                    uu____13856))
                           in
                        FStar_All.pipe_right uu____13840
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____13784 uu____13838
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____13877 =
             let uu____13894 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____13894  in
           match uu____13877 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____13984 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____13984
                 then ()
                 else
                   (let uu____13989 = lec_hd  in
                    match uu____13989 with
                    | (lb1,uu____13997,uu____13998) ->
                        let uu____13999 = lec2  in
                        (match uu____13999 with
                         | (lb2,uu____14007,uu____14008) ->
                             let msg =
                               let uu____14011 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____14013 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____14011 uu____14013
                                in
                             let uu____14016 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____14016))
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
                 let uu____14084 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____14084
                 then ()
                 else
                   (let uu____14089 = lec_hd  in
                    match uu____14089 with
                    | (lb1,uu____14097,uu____14098) ->
                        let uu____14099 = lec2  in
                        (match uu____14099 with
                         | (lb2,uu____14107,uu____14108) ->
                             let msg =
                               let uu____14111 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____14113 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____14111 uu____14113
                                in
                             let uu____14116 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____14116))
                  in
               let lecs1 =
                 let uu____14127 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____14180 = univs_and_uvars_of_lec this_lec  in
                        match uu____14180 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____14127 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____14285 = lec_hd  in
                   match uu____14285 with
                   | (lbname,e,c) ->
                       let uu____14295 =
                         let uu____14301 =
                           let uu____14303 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____14305 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____14307 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____14303 uu____14305 uu____14307
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____14301)
                          in
                       let uu____14311 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____14295 uu____14311
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____14330 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____14330 with
                         | FStar_Pervasives_Native.Some uu____14339 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____14347 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____14351 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____14351 with
                              | (bs,kres) ->
                                  ((let uu____14395 =
                                      let uu____14396 =
                                        let uu____14399 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____14399
                                         in
                                      uu____14396.FStar_Syntax_Syntax.n  in
                                    match uu____14395 with
                                    | FStar_Syntax_Syntax.Tm_type uu____14400
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____14404 =
                                          let uu____14406 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____14406  in
                                        if uu____14404
                                        then fail1 kres
                                        else ()
                                    | uu____14411 -> fail1 kres);
                                   (let a =
                                      let uu____14413 =
                                        let uu____14416 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _14419  ->
                                             FStar_Pervasives_Native.Some
                                               _14419) uu____14416
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____14413
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____14427 ->
                                          let uu____14436 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____14436
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
                      (fun uu____14539  ->
                         match uu____14539 with
                         | (lbname,e,c) ->
                             let uu____14585 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____14646 ->
                                   let uu____14659 = (e, c)  in
                                   (match uu____14659 with
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
                                                (fun uu____14699  ->
                                                   match uu____14699 with
                                                   | (x,uu____14705) ->
                                                       let uu____14706 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____14706)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____14724 =
                                                let uu____14726 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____14726
                                                 in
                                              if uu____14724
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
                                          let uu____14735 =
                                            let uu____14736 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____14736.FStar_Syntax_Syntax.n
                                             in
                                          match uu____14735 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____14761 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____14761 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____14772 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____14776 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____14776, gen_tvars))
                                in
                             (match uu____14585 with
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
        (let uu____14923 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____14923
         then
           let uu____14926 =
             let uu____14928 =
               FStar_List.map
                 (fun uu____14943  ->
                    match uu____14943 with
                    | (lb,uu____14952,uu____14953) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____14928 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____14926
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____14979  ->
                match uu____14979 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____15008 = gen env is_rec lecs  in
           match uu____15008 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____15107  ->
                       match uu____15107 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____15169 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____15169
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____15217  ->
                           match uu____15217 with
                           | (l,us,e,c,gvs) ->
                               let uu____15251 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____15253 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____15255 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____15257 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____15259 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____15251 uu____15253 uu____15255
                                 uu____15257 uu____15259))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____15304  ->
                match uu____15304 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____15348 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____15348, t, c, gvs)) univnames_lecs
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
              (let uu____15413 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                  in
               match uu____15413 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____15419 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _15422  -> FStar_Pervasives_Native.Some _15422)
                     uu____15419)
             in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1779_15442 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1779_15442.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1779_15442.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____15443 -> e2  in
          let uu____15444 = maybe_coerce_lc env1 e lc t2  in
          match uu____15444 with
          | (e1,lc1,g_c) ->
              let uu____15460 =
                check1 env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____15460 with
               | FStar_Pervasives_Native.None  ->
                   let uu____15469 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____15475 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____15469 uu____15475
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____15484 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____15484
                     then
                       let uu____15489 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____15489
                     else ());
                    (let uu____15495 = decorate e1 t2  in
                     let uu____15496 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (uu____15495, lc1, uu____15496))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____15524 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____15524
         then
           let uu____15527 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____15527
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____15541 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____15541 with
         | (c,g_c) ->
             let uu____15553 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____15553
             then
               let uu____15561 =
                 let uu____15563 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____15563  in
               (uu____15561, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____15571 =
                    let uu____15572 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____15572
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____15571
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____15573 = check_trivial_precondition env c1  in
                match uu____15573 with
                | (ct,vc,g_pre) ->
                    ((let uu____15589 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____15589
                      then
                        let uu____15594 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____15594
                      else ());
                     (let uu____15599 =
                        let uu____15601 =
                          let uu____15602 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____15602  in
                        discharge uu____15601  in
                      let uu____15603 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____15599, uu____15603)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_15637 =
        match uu___8_15637 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____15647)::[] -> f fst1
        | uu____15672 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____15684 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____15684
          (fun _15685  -> FStar_TypeChecker_Common.NonTrivial _15685)
         in
      let op_or_e e =
        let uu____15696 =
          let uu____15697 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____15697  in
        FStar_All.pipe_right uu____15696
          (fun _15700  -> FStar_TypeChecker_Common.NonTrivial _15700)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _15707  -> FStar_TypeChecker_Common.NonTrivial _15707)
         in
      let op_or_t t =
        let uu____15718 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____15718
          (fun _15721  -> FStar_TypeChecker_Common.NonTrivial _15721)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _15728  -> FStar_TypeChecker_Common.NonTrivial _15728)
         in
      let short_op_ite uu___9_15734 =
        match uu___9_15734 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____15744)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____15771)::[] ->
            let uu____15812 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____15812
              (fun _15813  -> FStar_TypeChecker_Common.NonTrivial _15813)
        | uu____15814 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____15826 =
          let uu____15834 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____15834)  in
        let uu____15842 =
          let uu____15852 =
            let uu____15860 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____15860)  in
          let uu____15868 =
            let uu____15878 =
              let uu____15886 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____15886)  in
            let uu____15894 =
              let uu____15904 =
                let uu____15912 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____15912)  in
              let uu____15920 =
                let uu____15930 =
                  let uu____15938 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____15938)  in
                [uu____15930; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____15904 :: uu____15920  in
            uu____15878 :: uu____15894  in
          uu____15852 :: uu____15868  in
        uu____15826 :: uu____15842  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____16000 =
            FStar_Util.find_map table
              (fun uu____16015  ->
                 match uu____16015 with
                 | (x,mk1) ->
                     let uu____16032 = FStar_Ident.lid_equals x lid  in
                     if uu____16032
                     then
                       let uu____16037 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____16037
                     else FStar_Pervasives_Native.None)
             in
          (match uu____16000 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____16041 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____16049 =
      let uu____16050 = FStar_Syntax_Util.un_uinst l  in
      uu____16050.FStar_Syntax_Syntax.n  in
    match uu____16049 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____16055 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____16091)::uu____16092 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____16111 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____16120,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____16121))::uu____16122 -> bs
      | uu____16140 ->
          let uu____16141 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____16141 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____16145 =
                 let uu____16146 = FStar_Syntax_Subst.compress t  in
                 uu____16146.FStar_Syntax_Syntax.n  in
               (match uu____16145 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____16150) ->
                    let uu____16171 =
                      FStar_Util.prefix_until
                        (fun uu___10_16211  ->
                           match uu___10_16211 with
                           | (uu____16219,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____16220)) ->
                               false
                           | uu____16225 -> true) bs'
                       in
                    (match uu____16171 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____16261,uu____16262) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____16334,uu____16335) ->
                         let uu____16408 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____16428  ->
                                   match uu____16428 with
                                   | (x,uu____16437) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____16408
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____16486  ->
                                     match uu____16486 with
                                     | (x,i) ->
                                         let uu____16505 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____16505, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____16516 -> bs))
  
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
            let uu____16545 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____16545
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
          let uu____16576 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____16576
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
        (let uu____16619 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____16619
         then
           ((let uu____16624 = FStar_Ident.text_of_lid lident  in
             d uu____16624);
            (let uu____16626 = FStar_Ident.text_of_lid lident  in
             let uu____16628 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____16626 uu____16628))
         else ());
        (let fv =
           let uu____16634 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____16634
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
         let uu____16646 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1940_16648 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1940_16648.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1940_16648.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1940_16648.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1940_16648.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___1940_16648.FStar_Syntax_Syntax.sigopts)
           }), uu____16646))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_16666 =
        match uu___11_16666 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____16669 -> false  in
      let reducibility uu___12_16677 =
        match uu___12_16677 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____16684 -> false  in
      let assumption uu___13_16692 =
        match uu___13_16692 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____16696 -> false  in
      let reification uu___14_16704 =
        match uu___14_16704 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____16707 -> true
        | uu____16709 -> false  in
      let inferred uu___15_16717 =
        match uu___15_16717 with
        | FStar_Syntax_Syntax.Discriminator uu____16719 -> true
        | FStar_Syntax_Syntax.Projector uu____16721 -> true
        | FStar_Syntax_Syntax.RecordType uu____16727 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____16737 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____16750 -> false  in
      let has_eq uu___16_16758 =
        match uu___16_16758 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____16762 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____16841 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____16848 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____16881 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____16881))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____16912 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____16912
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
           | FStar_Syntax_Syntax.Sig_bundle uu____16932 ->
               let uu____16941 =
                 let uu____16943 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_16949  ->
                           match uu___17_16949 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____16952 -> false))
                    in
                 Prims.op_Negation uu____16943  in
               if uu____16941
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____16959 -> ()
           | uu____16966 ->
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
      let uu____16980 =
        let uu____16982 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_16988  ->
                  match uu___18_16988 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____16991 -> false))
           in
        FStar_All.pipe_right uu____16982 Prims.op_Negation  in
      if uu____16980
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____17012 =
            let uu____17018 =
              let uu____17020 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____17020 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____17018)  in
          FStar_Errors.raise_error uu____17012 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____17038 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____17046 =
            let uu____17048 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____17048  in
          if uu____17046 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____17059),uu____17060) ->
              ((let uu____17072 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____17072
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____17081 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____17081
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____17092 ->
              ((let uu____17102 =
                  let uu____17104 =
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
                  Prims.op_Negation uu____17104  in
                if uu____17102 then err'1 () else ());
               (let uu____17114 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_17120  ->
                           match uu___19_17120 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____17123 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____17114
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____17129 ->
              let uu____17136 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____17136 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____17144 ->
              let uu____17151 =
                let uu____17153 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____17153  in
              if uu____17151 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____17163 ->
              let uu____17164 =
                let uu____17166 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____17166  in
              if uu____17164 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____17176 ->
              let uu____17189 =
                let uu____17191 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____17191  in
              if uu____17189 then err'1 () else ()
          | uu____17201 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____17240 =
          let uu____17241 = FStar_Syntax_Subst.compress t1  in
          uu____17241.FStar_Syntax_Syntax.n  in
        match uu____17240 with
        | FStar_Syntax_Syntax.Tm_arrow uu____17245 ->
            let uu____17260 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____17260 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____17293;
               FStar_Syntax_Syntax.index = uu____17294;
               FStar_Syntax_Syntax.sort = t2;_},uu____17296)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____17305) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____17331) ->
            descend env head1
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____17337 -> false
      
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
        (let uu____17347 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____17347
         then
           let uu____17352 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____17352
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
                  let uu____17417 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____17417 r  in
                let uu____17427 =
                  let uu____17428 = FStar_Syntax_Subst.compress signature  in
                  uu____17428.FStar_Syntax_Syntax.n  in
                match uu____17427 with
                | FStar_Syntax_Syntax.Tm_arrow (bs,uu____17436) ->
                    let bs1 = FStar_Syntax_Subst.open_binders bs  in
                    (match bs1 with
                     | a::bs2 ->
                         let uu____17484 =
                           FStar_TypeChecker_Env.uvars_for_binders env bs2
                             [FStar_Syntax_Syntax.NT
                                ((FStar_Pervasives_Native.fst a), a_tm)]
                             (fun b  ->
                                let uu____17499 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____17501 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format3
                                  "uvar for binder %s when creating a fresh repr for %s at %s"
                                  uu____17499 eff_name.FStar_Ident.str
                                  uu____17501) r
                            in
                         (match uu____17484 with
                          | (is,g) ->
                              let uu____17514 =
                                match repr_ts_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let eff_c =
                                      let uu____17516 =
                                        let uu____17517 =
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
                                            uu____17517;
                                          FStar_Syntax_Syntax.flags = []
                                        }  in
                                      FStar_Syntax_Syntax.mk_Comp uu____17516
                                       in
                                    let uu____17536 =
                                      let uu____17543 =
                                        let uu____17544 =
                                          let uu____17559 =
                                            let uu____17568 =
                                              FStar_Syntax_Syntax.null_binder
                                                FStar_Syntax_Syntax.t_unit
                                               in
                                            [uu____17568]  in
                                          (uu____17559, eff_c)  in
                                        FStar_Syntax_Syntax.Tm_arrow
                                          uu____17544
                                         in
                                      FStar_Syntax_Syntax.mk uu____17543  in
                                    uu____17536 FStar_Pervasives_Native.None
                                      r
                                | FStar_Pervasives_Native.Some repr_ts ->
                                    let repr =
                                      let uu____17599 =
                                        FStar_TypeChecker_Env.inst_tscheme_with
                                          repr_ts [u]
                                         in
                                      FStar_All.pipe_right uu____17599
                                        FStar_Pervasives_Native.snd
                                       in
                                    let uu____17608 =
                                      let uu____17613 =
                                        FStar_List.map
                                          FStar_Syntax_Syntax.as_arg (a_tm ::
                                          is)
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app repr
                                        uu____17613
                                       in
                                    uu____17608 FStar_Pervasives_Native.None
                                      r
                                 in
                              (uu____17514, g))
                     | uu____17622 -> fail1 signature)
                | uu____17623 -> fail1 signature
  
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
              let uu____17655 =
                let uu____17660 =
                  FStar_TypeChecker_Env.try_lookup_and_inst_lid env [u]
                    eff_name
                   in
                FStar_All.pipe_right uu____17660 FStar_Util.must  in
              FStar_All.pipe_right uu____17655 FStar_Pervasives_Native.fst
               in
            let repr_ts_opt =
              let uu____17688 =
                FStar_TypeChecker_Env.effect_decl_opt env eff_name  in
              FStar_Util.bind_opt uu____17688
                (fun x  ->
                   let uu____17712 =
                     FStar_All.pipe_right x FStar_Pervasives_Native.fst  in
                   FStar_All.pipe_right uu____17712
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
              let uu____17756 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____17756 with
              | (uu____17761,sig_tm) ->
                  let fail1 t =
                    let uu____17769 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____17769 r  in
                  let uu____17775 =
                    let uu____17776 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____17776.FStar_Syntax_Syntax.n  in
                  (match uu____17775 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____17780) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____17803)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____17825 -> fail1 sig_tm)
                   | uu____17826 -> fail1 sig_tm)
  
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
          (let uu____17857 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____17857
           then
             let uu____17862 = FStar_Syntax_Print.comp_to_string c  in
             let uu____17864 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____17862 uu____17864
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let effect_args_from_repr repr is_layered1 =
             let err uu____17894 =
               let uu____17895 =
                 let uu____17901 =
                   let uu____17903 = FStar_Syntax_Print.term_to_string repr
                      in
                   let uu____17905 = FStar_Util.string_of_bool is_layered1
                      in
                   FStar_Util.format2
                     "Could not get effect args from repr %s with is_layered %s"
                     uu____17903 uu____17905
                    in
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____17901)  in
               FStar_Errors.raise_error uu____17895 r  in
             let repr1 = FStar_Syntax_Subst.compress repr  in
             if is_layered1
             then
               match repr1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_app (uu____17917,uu____17918::is) ->
                   FStar_All.pipe_right is
                     (FStar_List.map FStar_Pervasives_Native.fst)
               | uu____17986 -> err ()
             else
               (match repr1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (uu____17991,c1) ->
                    let uu____18013 =
                      FStar_All.pipe_right c1
                        FStar_Syntax_Util.comp_to_comp_typ
                       in
                    FStar_All.pipe_right uu____18013
                      (fun ct  ->
                         FStar_All.pipe_right
                           ct.FStar_Syntax_Syntax.effect_args
                           (FStar_List.map FStar_Pervasives_Native.fst))
                | uu____18048 -> err ())
              in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____18050 =
             let uu____18061 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____18062 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____18061, (ct.FStar_Syntax_Syntax.result_typ), uu____18062)
              in
           match uu____18050 with
           | (u,a,c_is) ->
               let uu____18110 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____18110 with
                | (uu____18119,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____18130 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____18132 = FStar_Ident.string_of_lid tgt  in
                      let uu____18134 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____18130 uu____18132 s uu____18134
                       in
                    let uu____18137 =
                      let uu____18170 =
                        let uu____18171 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____18171.FStar_Syntax_Syntax.n  in
                      match uu____18170 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____18235 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____18235 with
                           | (a_b::bs1,c2) ->
                               let uu____18295 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               let uu____18357 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____18295, uu____18357))
                      | uu____18384 ->
                          let uu____18385 =
                            let uu____18391 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____18391)
                             in
                          FStar_Errors.raise_error uu____18385 r
                       in
                    (match uu____18137 with
                     | (a_b,(rest_bs,f_b::[]),lift_ct) ->
                         let uu____18509 =
                           let uu____18516 =
                             let uu____18517 =
                               let uu____18518 =
                                 let uu____18525 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____18525, a)  in
                               FStar_Syntax_Syntax.NT uu____18518  in
                             [uu____18517]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____18516
                             (fun b  ->
                                let uu____18542 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____18544 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____18546 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____18548 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____18542 uu____18544 uu____18546
                                  uu____18548) r
                            in
                         (match uu____18509 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____18562 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____18562
                                then
                                  let uu____18567 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____18576 =
                                             let uu____18578 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____18578
                                              in
                                           Prims.op_Hat s uu____18576) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____18567
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____18609 =
                                           let uu____18616 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____18616, t)  in
                                         FStar_Syntax_Syntax.NT uu____18609)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____18635 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____18635
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____18641 =
                                      let uu____18643 =
                                        FStar_TypeChecker_Env.norm_eff_name
                                          env
                                          ct.FStar_Syntax_Syntax.effect_name
                                         in
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env uu____18643
                                       in
                                    effect_args_from_repr f_sort uu____18641
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____18651 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____18651)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let is =
                                  let uu____18655 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____18655
                                   in
                                let c1 =
                                  let uu____18658 =
                                    let uu____18659 =
                                      let uu____18670 =
                                        FStar_All.pipe_right is
                                          (FStar_List.map
                                             (FStar_Syntax_Subst.subst substs))
                                         in
                                      FStar_All.pipe_right uu____18670
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.as_arg)
                                       in
                                    {
                                      FStar_Syntax_Syntax.comp_univs =
                                        (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                      FStar_Syntax_Syntax.effect_name = tgt;
                                      FStar_Syntax_Syntax.result_typ = a;
                                      FStar_Syntax_Syntax.effect_args =
                                        uu____18659;
                                      FStar_Syntax_Syntax.flags =
                                        (ct.FStar_Syntax_Syntax.flags)
                                    }  in
                                  FStar_Syntax_Syntax.mk_Comp uu____18658  in
                                (let uu____18690 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "LayeredEffects")
                                    in
                                 if uu____18690
                                 then
                                   let uu____18695 =
                                     FStar_Syntax_Print.comp_to_string c1  in
                                   FStar_Util.print1 "} Lifted comp: %s\n"
                                     uu____18695
                                 else ());
                                (let uu____18700 =
                                   FStar_TypeChecker_Env.conj_guard g guard_f
                                    in
                                 (c1, uu____18700))))))))
  
let lift_tf_layered_effect_term :
  'Auu____18714 .
    'Auu____18714 ->
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
              let uu____18743 =
                let uu____18748 =
                  FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____18748
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____18743 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____18791 =
                let uu____18792 =
                  let uu____18795 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____18795
                    FStar_Syntax_Subst.compress
                   in
                uu____18792.FStar_Syntax_Syntax.n  in
              match uu____18791 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____18818::bs,uu____18820)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____18860 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____18860
                    FStar_Pervasives_Native.fst
              | uu____18966 ->
                  let uu____18967 =
                    let uu____18973 =
                      let uu____18975 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____18975
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____18973)  in
                  FStar_Errors.raise_error uu____18967
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____19002 = FStar_Syntax_Syntax.as_arg a  in
              let uu____19011 =
                let uu____19022 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____19058  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____19065 =
                  let uu____19076 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____19076]  in
                FStar_List.append uu____19022 uu____19065  in
              uu____19002 :: uu____19011  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub1  ->
      let uu____19140 =
        (let uu____19144 =
           FStar_All.pipe_right sub1.FStar_Syntax_Syntax.source
             (FStar_TypeChecker_Env.norm_eff_name env)
            in
         FStar_All.pipe_right uu____19144
           (FStar_TypeChecker_Env.is_layered_effect env))
          ||
          (FStar_All.pipe_right sub1.FStar_Syntax_Syntax.target
             (FStar_TypeChecker_Env.is_layered_effect env))
         in
      if uu____19140
      then
        let uu____19148 =
          let uu____19161 =
            FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub1.FStar_Syntax_Syntax.target uu____19161
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____19148;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub1))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____19196 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____19196 with
           | (uu____19205,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____19224 =
                 let uu____19225 =
                   let uu___2302_19226 = ct  in
                   let uu____19227 =
                     let uu____19238 =
                       let uu____19247 =
                         let uu____19248 =
                           let uu____19255 =
                             let uu____19256 =
                               let uu____19273 =
                                 let uu____19284 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____19284; wp]  in
                               (lift_t, uu____19273)  in
                             FStar_Syntax_Syntax.Tm_app uu____19256  in
                           FStar_Syntax_Syntax.mk uu____19255  in
                         uu____19248 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____19247
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____19238]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2302_19226.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub1.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2302_19226.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____19227;
                     FStar_Syntax_Syntax.flags =
                       (uu___2302_19226.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____19225  in
               (uu____19224, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____19384 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____19384 with
           | (uu____19391,lift_t) ->
               let uu____19393 =
                 let uu____19400 =
                   let uu____19401 =
                     let uu____19418 =
                       let uu____19429 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____19438 =
                         let uu____19449 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____19458 =
                           let uu____19469 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____19469]  in
                         uu____19449 :: uu____19458  in
                       uu____19429 :: uu____19438  in
                     (lift_t, uu____19418)  in
                   FStar_Syntax_Syntax.Tm_app uu____19401  in
                 FStar_Syntax_Syntax.mk uu____19400  in
               uu____19393 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____19522 =
           let uu____19535 =
             FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____19535 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____19522;
           FStar_TypeChecker_Env.mlift_term =
             (match sub1.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____19571  ->
                        fun uu____19572  -> fun e  -> FStar_Util.return_all e))
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
        let uu____19602 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____19602 with
        | (uu____19607,t) ->
            let err n1 =
              let uu____19617 =
                let uu____19623 =
                  let uu____19625 = FStar_Ident.string_of_lid datacon  in
                  let uu____19627 = FStar_Util.string_of_int n1  in
                  let uu____19629 = FStar_Util.string_of_int index1  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____19625 uu____19627 uu____19629
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____19623)
                 in
              let uu____19633 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____19617 uu____19633  in
            let uu____19634 =
              let uu____19635 = FStar_Syntax_Subst.compress t  in
              uu____19635.FStar_Syntax_Syntax.n  in
            (match uu____19634 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____19639) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____19694  ->
                           match uu____19694 with
                           | (uu____19702,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____19711 -> true)))
                    in
                 if (FStar_List.length bs1) <= index1
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index1  in
                    let uu____19743 =
                      FStar_Syntax_Util.mk_field_projector_name datacon
                        (FStar_Pervasives_Native.fst b) index1
                       in
                    FStar_All.pipe_right uu____19743
                      FStar_Pervasives_Native.fst)
             | uu____19754 -> err Prims.int_zero)
  