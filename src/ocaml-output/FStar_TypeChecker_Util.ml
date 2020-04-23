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
          FStar_Syntax_Syntax.lbunivs = univ_vars;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____339;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____341;
          FStar_Syntax_Syntax.lbpos = uu____342;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____377 = FStar_Syntax_Subst.open_univ_vars univ_vars e
                  in
               (match uu____377 with
                | (univ_vars1,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
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
                    (univ_vars1, t2, true))
           | uu____575 ->
               let uu____576 = FStar_Syntax_Subst.open_univ_vars univ_vars t1
                  in
               (match uu____576 with
                | (univ_vars1,t2) -> (univ_vars1, t2, false)))
  
let rec (decorated_pattern_as_term :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun pat  ->
    let mk f =
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
        let uu____702 = mk (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____702)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____706 = mk (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____706)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____710 = mk (FStar_Syntax_Syntax.Tm_name x)  in
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
               mk uu____891  in
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
         | hd::uu____972 -> FStar_Pervasives_Native.Some hd)
  
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
            let uu____1088 =
              let uu____1089 =
                let uu____1100 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____1100]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____1089;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____1088
  
let (mk_comp :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  = fun md  -> mk_comp_l md.FStar_Syntax_Syntax.mname 
let (mk_wp_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term ->
            FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun ed  ->
      fun u_a  ->
        fun a  ->
          fun e  ->
            fun r  ->
              let ret_wp =
                FStar_All.pipe_right ed
                  FStar_Syntax_Util.get_return_vc_combinator
                 in
              let wp =
                let uu____1190 =
                  let uu____1195 =
                    FStar_TypeChecker_Env.inst_effect_fun_with [u_a] env ed
                      ret_wp
                     in
                  let uu____1196 =
                    let uu____1197 = FStar_Syntax_Syntax.as_arg a  in
                    let uu____1206 =
                      let uu____1217 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____1217]  in
                    uu____1197 :: uu____1206  in
                  FStar_Syntax_Syntax.mk_Tm_app uu____1195 uu____1196  in
                uu____1190 FStar_Pervasives_Native.None r  in
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
  fun env  ->
    fun ed  ->
      fun u_a  ->
        fun a  ->
          fun e  ->
            fun r  ->
              (let uu____1290 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "LayeredEffectsApp")
                  in
               if uu____1290
               then
                 let uu____1295 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname  in
                 let uu____1297 = FStar_Syntax_Print.univ_to_string u_a  in
                 let uu____1299 = FStar_Syntax_Print.term_to_string a  in
                 let uu____1301 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print4
                   "Computing %s.return for u_a:%s, a:%s, and e:%s{\n"
                   uu____1295 uu____1297 uu____1299 uu____1301
               else ());
              (let uu____1306 =
                 let uu____1311 =
                   FStar_All.pipe_right ed
                     FStar_Syntax_Util.get_return_vc_combinator
                    in
                 FStar_TypeChecker_Env.inst_tscheme_with uu____1311 [u_a]  in
               match uu____1306 with
               | (uu____1316,return_t) ->
                   let return_t_shape_error s =
                     let uu____1331 =
                       let uu____1333 =
                         FStar_Ident.string_of_lid
                           ed.FStar_Syntax_Syntax.mname
                          in
                       let uu____1335 =
                         FStar_Syntax_Print.term_to_string return_t  in
                       FStar_Util.format3
                         "%s.return %s does not have proper shape (reason:%s)"
                         uu____1333 uu____1335 s
                        in
                     (FStar_Errors.Fatal_UnexpectedEffect, uu____1331)  in
                   let uu____1339 =
                     let uu____1368 =
                       let uu____1369 = FStar_Syntax_Subst.compress return_t
                          in
                       uu____1369.FStar_Syntax_Syntax.n  in
                     match uu____1368 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                         (FStar_List.length bs) >= (Prims.of_int (2)) ->
                         let uu____1429 = FStar_Syntax_Subst.open_comp bs c
                            in
                         (match uu____1429 with
                          | (a_b::x_b::bs1,c1) ->
                              let uu____1498 =
                                FStar_Syntax_Util.comp_to_comp_typ c1  in
                              (a_b, x_b, bs1, uu____1498))
                     | uu____1519 ->
                         let uu____1520 =
                           return_t_shape_error
                             "Either not an arrow or not enough binders"
                            in
                         FStar_Errors.raise_error uu____1520 r
                      in
                   (match uu____1339 with
                    | (a_b,x_b,rest_bs,return_ct) ->
                        let uu____1603 =
                          let uu____1610 =
                            let uu____1611 =
                              let uu____1612 =
                                let uu____1619 =
                                  FStar_All.pipe_right a_b
                                    FStar_Pervasives_Native.fst
                                   in
                                (uu____1619, a)  in
                              FStar_Syntax_Syntax.NT uu____1612  in
                            let uu____1630 =
                              let uu____1633 =
                                let uu____1634 =
                                  let uu____1641 =
                                    FStar_All.pipe_right x_b
                                      FStar_Pervasives_Native.fst
                                     in
                                  (uu____1641, e)  in
                                FStar_Syntax_Syntax.NT uu____1634  in
                              [uu____1633]  in
                            uu____1611 :: uu____1630  in
                          FStar_TypeChecker_Env.uvars_for_binders env rest_bs
                            uu____1610
                            (fun b  ->
                               let uu____1657 =
                                 FStar_Syntax_Print.binder_to_string b  in
                               let uu____1659 =
                                 let uu____1661 =
                                   FStar_Ident.string_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Util.format1 "%s.return" uu____1661
                                  in
                               let uu____1664 = FStar_Range.string_of_range r
                                  in
                               FStar_Util.format3
                                 "implicit for binder %s of %s at %s"
                                 uu____1657 uu____1659 uu____1664) r
                           in
                        (match uu____1603 with
                         | (rest_bs_uvars,g_uvars) ->
                             let subst =
                               FStar_List.map2
                                 (fun b  ->
                                    fun t  ->
                                      let uu____1701 =
                                        let uu____1708 =
                                          FStar_All.pipe_right b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____1708, t)  in
                                      FStar_Syntax_Syntax.NT uu____1701) (a_b
                                 :: x_b :: rest_bs) (a :: e :: rest_bs_uvars)
                                in
                             let is =
                               let uu____1734 =
                                 let uu____1737 =
                                   FStar_Syntax_Subst.compress
                                     return_ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 let uu____1738 =
                                   FStar_Syntax_Util.is_layered ed  in
                                 let uu____1740 =
                                   let uu____1742 =
                                     FStar_Ident.string_of_lid
                                       ed.FStar_Syntax_Syntax.mname
                                      in
                                   let uu____1744 =
                                     FStar_Syntax_Print.term_to_string
                                       return_ct.FStar_Syntax_Syntax.result_typ
                                      in
                                   FStar_Util.format2
                                     "return result type for %s is not a repr (%s)"
                                     uu____1742 uu____1744
                                    in
                                 FStar_Syntax_Util.effect_indices_from_repr
                                   uu____1737 uu____1738 r uu____1740
                                  in
                               FStar_All.pipe_right uu____1734
                                 (FStar_List.map
                                    (FStar_Syntax_Subst.subst subst))
                                in
                             let c =
                               let uu____1752 =
                                 let uu____1753 =
                                   FStar_All.pipe_right is
                                     (FStar_List.map
                                        FStar_Syntax_Syntax.as_arg)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs = [u_a];
                                   FStar_Syntax_Syntax.effect_name =
                                     (ed.FStar_Syntax_Syntax.mname);
                                   FStar_Syntax_Syntax.result_typ = a;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____1753;
                                   FStar_Syntax_Syntax.flags = []
                                 }  in
                               FStar_Syntax_Syntax.mk_Comp uu____1752  in
                             ((let uu____1777 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffectsApp")
                                  in
                               if uu____1777
                               then
                                 let uu____1782 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.print1 "} c after return %s\n"
                                   uu____1782
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
  fun env  ->
    fun ed  ->
      fun u_a  ->
        fun a  ->
          fun e  ->
            fun r  ->
              let uu____1826 =
                FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
              if uu____1826
              then mk_indexed_return env ed u_a a e r
              else
                (let uu____1836 = mk_wp_return env ed u_a a e r  in
                 (uu____1836, FStar_TypeChecker_Env.trivial_guard))
  
let (lift_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp_typ ->
      FStar_TypeChecker_Env.mlift ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c  ->
      fun lift  ->
        let uu____1861 =
          FStar_All.pipe_right
            (let uu___231_1863 = c  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___231_1863.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___231_1863.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ =
                 (uu___231_1863.FStar_Syntax_Syntax.result_typ);
               FStar_Syntax_Syntax.effect_args =
                 (uu___231_1863.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags = []
             }) FStar_Syntax_Syntax.mk_Comp
           in
        FStar_All.pipe_right uu____1861
          (lift.FStar_TypeChecker_Env.mlift_wp env)
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1_in  ->
      fun l2_in  ->
        let uu____1884 =
          let uu____1889 = FStar_TypeChecker_Env.norm_eff_name env l1_in  in
          let uu____1890 = FStar_TypeChecker_Env.norm_eff_name env l2_in  in
          (uu____1889, uu____1890)  in
        match uu____1884 with
        | (l1,l2) ->
            let uu____1893 = FStar_TypeChecker_Env.join_opt env l1 l2  in
            (match uu____1893 with
             | FStar_Pervasives_Native.Some (m,uu____1903,uu____1904) -> m
             | FStar_Pervasives_Native.None  ->
                 let uu____1917 =
                   FStar_TypeChecker_Env.exists_polymonadic_bind env l1 l2
                    in
                 (match uu____1917 with
                  | FStar_Pervasives_Native.Some (m,uu____1931) -> m
                  | FStar_Pervasives_Native.None  ->
                      let uu____1964 =
                        let uu____1970 =
                          let uu____1972 =
                            FStar_Syntax_Print.lid_to_string l1_in  in
                          let uu____1974 =
                            FStar_Syntax_Print.lid_to_string l2_in  in
                          FStar_Util.format2
                            "Effects %s and %s cannot be composed" uu____1972
                            uu____1974
                           in
                        (FStar_Errors.Fatal_EffectsCannotBeComposed,
                          uu____1970)
                         in
                      FStar_Errors.raise_error uu____1964
                        env.FStar_TypeChecker_Env.range))
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____1994 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2)
           in
        if uu____1994
        then FStar_Parser_Const.effect_Tot_lid
        else
          join_effects env c1.FStar_TypeChecker_Common.eff_name
            c2.FStar_TypeChecker_Common.eff_name
  
type lift_context =
  | Lift_for_bind 
  | Lift_for_match 
let (uu___is_Lift_for_bind : lift_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lift_for_bind  -> true | uu____2008 -> false
  
let (uu___is_Lift_for_match : lift_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lift_for_match  -> true | uu____2019 -> false
  
let (lift_comps_sep_guards :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
          lift_context ->
            (FStar_Ident.lident * FStar_Syntax_Syntax.comp *
              FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t *
              FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        fun b  ->
          fun lift_context1  ->
            let c11 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
            let c21 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
            let uu____2073 =
              FStar_TypeChecker_Env.join_opt env
                c11.FStar_Syntax_Syntax.effect_name
                c21.FStar_Syntax_Syntax.effect_name
               in
            match uu____2073 with
            | FStar_Pervasives_Native.Some (m,lift1,lift2) ->
                let uu____2101 = lift_comp env c11 lift1  in
                (match uu____2101 with
                 | (c12,g1) ->
                     let uu____2118 =
                       if lift_context1 = Lift_for_match
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
                            FStar_TypeChecker_Env.push_binders env [x_a]  in
                          let uu____2157 = lift_comp env_x c21 lift2  in
                          match uu____2157 with
                          | (c22,g2) ->
                              let uu____2168 =
                                FStar_TypeChecker_Env.close_guard env 
                                  [x_a] g2
                                 in
                              (c22, uu____2168))
                        in
                     (match uu____2118 with
                      | (c22,g2) -> (m, c12, c22, g1, g2)))
            | FStar_Pervasives_Native.None  ->
                let rng = env.FStar_TypeChecker_Env.range  in
                let err uu____2215 =
                  let uu____2216 =
                    let uu____2222 =
                      let uu____2224 =
                        FStar_Syntax_Print.lid_to_string
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____2226 =
                        FStar_Syntax_Print.lid_to_string
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____2224
                        uu____2226
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____2222)
                     in
                  FStar_Errors.raise_error uu____2216 rng  in
                ((let uu____2241 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "LayeredEffectsApp")
                     in
                  if uu____2241
                  then
                    let uu____2246 =
                      let uu____2248 =
                        FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp
                         in
                      FStar_All.pipe_right uu____2248
                        FStar_Syntax_Print.comp_to_string
                       in
                    let uu____2250 =
                      let uu____2252 =
                        FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                         in
                      FStar_All.pipe_right uu____2252
                        FStar_Syntax_Print.comp_to_string
                       in
                    FStar_Util.print3
                      "Lifting comps %s and %s with lift context %s{\n"
                      uu____2246 uu____2250
                      (match lift_context1 with
                       | Lift_for_bind  -> "bind"
                       | Lift_for_match  -> "match")
                  else ());
                 if lift_context1 = Lift_for_bind
                 then err ()
                 else
                   (let bind_with_return ct ret_eff f_bind =
                      let x_bv =
                        FStar_Syntax_Syntax.gen_bv "x"
                          FStar_Pervasives_Native.None
                          ct.FStar_Syntax_Syntax.result_typ
                         in
                      let uu____2311 =
                        let uu____2316 =
                          FStar_TypeChecker_Env.push_bv env x_bv  in
                        let uu____2317 =
                          FStar_TypeChecker_Env.get_effect_decl env ret_eff
                           in
                        let uu____2318 =
                          FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
                        let uu____2319 = FStar_Syntax_Syntax.bv_to_name x_bv
                           in
                        mk_return uu____2316 uu____2317 uu____2318
                          ct.FStar_Syntax_Syntax.result_typ uu____2319 rng
                         in
                      match uu____2311 with
                      | (c_ret,g_ret) ->
                          let uu____2326 =
                            let uu____2331 =
                              FStar_Syntax_Util.comp_to_comp_typ c_ret  in
                            f_bind env ct (FStar_Pervasives_Native.Some x_bv)
                              uu____2331 [] rng
                             in
                          (match uu____2326 with
                           | (c,g_bind) ->
                               let uu____2338 =
                                 FStar_TypeChecker_Env.conj_guard g_ret
                                   g_bind
                                  in
                               (c, uu____2338))
                       in
                    let try_lift c12 c22 =
                      let p_bind_opt =
                        FStar_TypeChecker_Env.exists_polymonadic_bind env
                          c12.FStar_Syntax_Syntax.effect_name
                          c22.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____2383 =
                        FStar_All.pipe_right p_bind_opt FStar_Util.is_some
                         in
                      if uu____2383
                      then
                        let uu____2419 =
                          FStar_All.pipe_right p_bind_opt FStar_Util.must  in
                        match uu____2419 with
                        | (p,f_bind) ->
                            let uu____2486 =
                              FStar_Ident.lid_equals p
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            (if uu____2486
                             then
                               let uu____2499 = bind_with_return c12 p f_bind
                                  in
                               match uu____2499 with
                               | (c13,g) ->
                                   let uu____2516 =
                                     let uu____2525 =
                                       FStar_Syntax_Syntax.mk_Comp c22  in
                                     ((c22.FStar_Syntax_Syntax.effect_name),
                                       c13, uu____2525, g)
                                      in
                                   FStar_Pervasives_Native.Some uu____2516
                             else FStar_Pervasives_Native.None)
                      else FStar_Pervasives_Native.None  in
                    let uu____2554 =
                      let uu____2565 = try_lift c11 c21  in
                      match uu____2565 with
                      | FStar_Pervasives_Native.Some (p,c12,c22,g) ->
                          (p, c12, c22, g,
                            FStar_TypeChecker_Env.trivial_guard)
                      | FStar_Pervasives_Native.None  ->
                          let uu____2606 = try_lift c21 c11  in
                          (match uu____2606 with
                           | FStar_Pervasives_Native.Some (p,c22,c12,g) ->
                               (p, c12, c22,
                                 FStar_TypeChecker_Env.trivial_guard, g)
                           | FStar_Pervasives_Native.None  -> err ())
                       in
                    match uu____2554 with
                    | (p,c12,c22,g1,g2) ->
                        ((let uu____2663 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "LayeredEffectsApp")
                             in
                          if uu____2663
                          then
                            let uu____2668 = FStar_Ident.string_of_lid p  in
                            let uu____2670 =
                              FStar_Syntax_Print.comp_to_string c12  in
                            let uu____2672 =
                              FStar_Syntax_Print.comp_to_string c22  in
                            FStar_Util.print3
                              "} Returning p %s, c1 %s, and c2 %s\n"
                              uu____2668 uu____2670 uu____2672
                          else ());
                         (p, c12, c22, g1, g2))))
  
let (lift_comps :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
          lift_context ->
            (FStar_Ident.lident * FStar_Syntax_Syntax.comp *
              FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        fun b  ->
          fun lift_context1  ->
            let uu____2723 = lift_comps_sep_guards env c1 c2 b lift_context1
               in
            match uu____2723 with
            | (l,c11,c21,g1,g2) ->
                let uu____2747 = FStar_TypeChecker_Env.conj_guard g1 g2  in
                (l, c11, c21, uu____2747)
  
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
          let uu____2803 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____2803
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2815 =
      let uu____2816 = FStar_Syntax_Subst.compress t  in
      uu____2816.FStar_Syntax_Syntax.n  in
    match uu____2815 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2820 -> true
    | uu____2836 -> false
  
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
              let uu____2906 =
                let uu____2908 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____2908  in
              if uu____2906
              then f
              else (let uu____2915 = reason1 ()  in label uu____2915 r f)
  
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
            let uu___378_2936 = g  in
            let uu____2937 =
              let uu____2938 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____2938  in
            {
              FStar_TypeChecker_Common.guard_f = uu____2937;
              FStar_TypeChecker_Common.deferred =
                (uu___378_2936.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___378_2936.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___378_2936.FStar_TypeChecker_Common.implicits)
            }
  
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2959 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____2959
        then c
        else
          (let uu____2964 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____2964
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close =
                  let uu____3006 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator
                     in
                  FStar_All.pipe_right uu____3006 FStar_Util.must  in
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____3034 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____3034]  in
                       let us =
                         let uu____3056 =
                           let uu____3059 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____3059]  in
                         u_res :: uu____3056  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____3065 =
                         let uu____3070 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md close
                            in
                         let uu____3071 =
                           let uu____3072 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____3081 =
                             let uu____3092 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____3101 =
                               let uu____3112 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____3112]  in
                             uu____3092 :: uu____3101  in
                           uu____3072 :: uu____3081  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3070 uu____3071
                          in
                       uu____3065 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____3154 = destruct_wp_comp c1  in
              match uu____3154 with
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
                let uu____3194 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____3194
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
                  let uu____3244 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs)
                     in
                  FStar_All.pipe_right uu____3244
                    (close_guard_implicits env false bs)))
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_3257  ->
            match uu___0_3257 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____3260 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____3285 =
            let uu____3288 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____3288 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____3285
            (fun c  ->
               (let uu____3312 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____3312) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____3316 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____3316)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____3327 = FStar_Syntax_Util.head_and_args' e  in
                match uu____3327 with
                | (head,uu____3344) ->
                    let uu____3365 =
                      let uu____3366 = FStar_Syntax_Util.un_uinst head  in
                      uu____3366.FStar_Syntax_Syntax.n  in
                    (match uu____3365 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____3371 =
                           let uu____3373 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____3373
                            in
                         Prims.op_Negation uu____3371
                     | uu____3374 -> true)))
              &&
              (let uu____3377 = should_not_inline_lc lc  in
               Prims.op_Negation uu____3377)
  
let (return_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun u_t_opt  ->
      fun t  ->
        fun v  ->
          let c =
            let uu____3405 =
              let uu____3407 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____3407  in
            if uu____3405
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____3414 = FStar_Syntax_Util.is_unit t  in
               if uu____3414
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
                    let uu____3423 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____3423
                    then FStar_Syntax_Syntax.tun
                    else
                      (let ret_wp =
                         FStar_All.pipe_right m
                           FStar_Syntax_Util.get_return_vc_combinator
                          in
                       let uu____3429 =
                         let uu____3430 =
                           let uu____3435 =
                             FStar_TypeChecker_Env.inst_effect_fun_with 
                               [u_t] env m ret_wp
                              in
                           let uu____3436 =
                             let uu____3437 = FStar_Syntax_Syntax.as_arg t
                                in
                             let uu____3446 =
                               let uu____3457 = FStar_Syntax_Syntax.as_arg v
                                  in
                               [uu____3457]  in
                             uu____3437 :: uu____3446  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3435
                             uu____3436
                            in
                         uu____3430 FStar_Pervasives_Native.None
                           v.FStar_Syntax_Syntax.pos
                          in
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Env.Beta;
                         FStar_TypeChecker_Env.NoFullNorm] env uu____3429)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____3491 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____3491
           then
             let uu____3496 =
               FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos  in
             let uu____3498 = FStar_Syntax_Print.term_to_string v  in
             let uu____3500 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____3496 uu____3498 uu____3500
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
  fun env  ->
    fun m  ->
      fun n  ->
        fun p  ->
          fun bind_t  ->
            fun ct1  ->
              fun b  ->
                fun ct2  ->
                  fun flags  ->
                    fun r1  ->
                      (let uu____3573 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LayeredEffectsApp")
                          in
                       if uu____3573
                       then
                         let uu____3578 =
                           let uu____3580 = FStar_Syntax_Syntax.mk_Comp ct1
                              in
                           FStar_Syntax_Print.comp_to_string uu____3580  in
                         let uu____3581 =
                           let uu____3583 = FStar_Syntax_Syntax.mk_Comp ct2
                              in
                           FStar_Syntax_Print.comp_to_string uu____3583  in
                         FStar_Util.print2 "Binding c1:%s and c2:%s {\n"
                           uu____3578 uu____3581
                       else ());
                      (let uu____3587 =
                         let uu____3594 =
                           FStar_TypeChecker_Env.get_effect_decl env m  in
                         let uu____3595 =
                           FStar_TypeChecker_Env.get_effect_decl env n  in
                         let uu____3596 =
                           FStar_TypeChecker_Env.get_effect_decl env p  in
                         (uu____3594, uu____3595, uu____3596)  in
                       match uu____3587 with
                       | (m_ed,n_ed,p_ed) ->
                           let uu____3604 =
                             let uu____3617 =
                               FStar_List.hd
                                 ct1.FStar_Syntax_Syntax.comp_univs
                                in
                             let uu____3618 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 ct1.FStar_Syntax_Syntax.effect_args
                                in
                             (uu____3617,
                               (ct1.FStar_Syntax_Syntax.result_typ),
                               uu____3618)
                              in
                           (match uu____3604 with
                            | (u1,t1,is1) ->
                                let uu____3662 =
                                  let uu____3675 =
                                    FStar_List.hd
                                      ct2.FStar_Syntax_Syntax.comp_univs
                                     in
                                  let uu____3676 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst
                                      ct2.FStar_Syntax_Syntax.effect_args
                                     in
                                  (uu____3675,
                                    (ct2.FStar_Syntax_Syntax.result_typ),
                                    uu____3676)
                                   in
                                (match uu____3662 with
                                 | (u2,t2,is2) ->
                                     let uu____3720 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         bind_t [u1; u2]
                                        in
                                     (match uu____3720 with
                                      | (uu____3729,bind_t1) ->
                                          let bind_t_shape_error s =
                                            let uu____3744 =
                                              let uu____3746 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t1
                                                 in
                                              FStar_Util.format2
                                                "bind %s does not have proper shape (reason:%s)"
                                                uu____3746 s
                                               in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu____3744)
                                             in
                                          let uu____3750 =
                                            let uu____3795 =
                                              let uu____3796 =
                                                FStar_Syntax_Subst.compress
                                                  bind_t1
                                                 in
                                              uu____3796.FStar_Syntax_Syntax.n
                                               in
                                            match uu____3795 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs,c) when
                                                (FStar_List.length bs) >=
                                                  (Prims.of_int (4))
                                                ->
                                                let uu____3872 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs c
                                                   in
                                                (match uu____3872 with
                                                 | (a_b::b_b::bs1,c1) ->
                                                     let uu____3957 =
                                                       let uu____3984 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2)))
                                                           bs1
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____3984
                                                         (fun uu____4069  ->
                                                            match uu____4069
                                                            with
                                                            | (l1,l2) ->
                                                                let uu____4150
                                                                  =
                                                                  FStar_List.hd
                                                                    l2
                                                                   in
                                                                let uu____4163
                                                                  =
                                                                  let uu____4170
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                  FStar_List.hd
                                                                    uu____4170
                                                                   in
                                                                (l1,
                                                                  uu____4150,
                                                                  uu____4163))
                                                        in
                                                     (match uu____3957 with
                                                      | (rest_bs,f_b,g_b) ->
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b, c1)))
                                            | uu____4330 ->
                                                let uu____4331 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders"
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____4331 r1
                                             in
                                          (match uu____3750 with
                                           | (a_b,b_b,rest_bs,f_b,g_b,bind_c)
                                               ->
                                               let uu____4456 =
                                                 let uu____4463 =
                                                   let uu____4464 =
                                                     let uu____4465 =
                                                       let uu____4472 =
                                                         FStar_All.pipe_right
                                                           a_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       (uu____4472, t1)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____4465
                                                      in
                                                   let uu____4483 =
                                                     let uu____4486 =
                                                       let uu____4487 =
                                                         let uu____4494 =
                                                           FStar_All.pipe_right
                                                             b_b
                                                             FStar_Pervasives_Native.fst
                                                            in
                                                         (uu____4494, t2)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____4487
                                                        in
                                                     [uu____4486]  in
                                                   uu____4464 :: uu____4483
                                                    in
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs uu____4463
                                                   (fun b1  ->
                                                      let uu____4510 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1
                                                         in
                                                      let uu____4512 =
                                                        let uu____4514 =
                                                          FStar_Ident.string_of_lid
                                                            m
                                                           in
                                                        let uu____4516 =
                                                          FStar_Ident.string_of_lid
                                                            n
                                                           in
                                                        let uu____4518 =
                                                          FStar_Ident.string_of_lid
                                                            p
                                                           in
                                                        FStar_Util.format3
                                                          "(%s, %s) |> %s"
                                                          uu____4514
                                                          uu____4516
                                                          uu____4518
                                                         in
                                                      let uu____4521 =
                                                        FStar_Range.string_of_range
                                                          r1
                                                         in
                                                      FStar_Util.format3
                                                        "implicit for binder %s of %s at %s"
                                                        uu____4510 uu____4512
                                                        uu____4521) r1
                                                  in
                                               (match uu____4456 with
                                                | (rest_bs_uvars,g_uvars) ->
                                                    let subst =
                                                      FStar_List.map2
                                                        (fun b1  ->
                                                           fun t  ->
                                                             let uu____4558 =
                                                               let uu____4565
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   b1
                                                                   FStar_Pervasives_Native.fst
                                                                  in
                                                               (uu____4565,
                                                                 t)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____4558)
                                                        (a_b :: b_b ::
                                                        rest_bs) (t1 :: t2 ::
                                                        rest_bs_uvars)
                                                       in
                                                    let f_guard =
                                                      let f_sort_is =
                                                        let uu____4594 =
                                                          let uu____4597 =
                                                            let uu____4598 =
                                                              let uu____4599
                                                                =
                                                                FStar_All.pipe_right
                                                                  f_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4599.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4598
                                                             in
                                                          let uu____4608 =
                                                            FStar_Syntax_Util.is_layered
                                                              m_ed
                                                             in
                                                          let uu____4610 =
                                                            let uu____4612 =
                                                              let uu____4614
                                                                =
                                                                let uu____4615
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    f_b
                                                                    FStar_Pervasives_Native.fst
                                                                   in
                                                                uu____4615.FStar_Syntax_Syntax.sort
                                                                 in
                                                              FStar_Syntax_Print.term_to_string
                                                                uu____4614
                                                               in
                                                            FStar_Util.format1
                                                              "bind f binder sort is not a repr (%s)"
                                                              uu____4612
                                                             in
                                                          FStar_Syntax_Util.effect_indices_from_repr
                                                            uu____4597
                                                            uu____4608 r1
                                                            uu____4610
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____4594
                                                          (FStar_List.map
                                                             (FStar_Syntax_Subst.subst
                                                                subst))
                                                         in
                                                      FStar_List.fold_left2
                                                        (fun g  ->
                                                           fun i1  ->
                                                             fun f_i1  ->
                                                               (let uu____4648
                                                                  =
                                                                  FStar_All.pipe_left
                                                                    (
                                                                    FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (
                                                                    FStar_Options.Other
                                                                    "LayeredEffectsRel")
                                                                   in
                                                                if uu____4648
                                                                then
                                                                  let uu____4653
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    i1  in
                                                                  let uu____4655
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    f_i1  in
                                                                  FStar_Util.print2
                                                                    "Layered effects teq %s = %s\n"
                                                                    uu____4653
                                                                    uu____4655
                                                                else ());
                                                               (let uu____4660
                                                                  =
                                                                  FStar_TypeChecker_Rel.teq
                                                                    env i1
                                                                    f_i1
                                                                   in
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  g
                                                                  uu____4660))
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
                                                        | FStar_Pervasives_Native.Some
                                                            x ->
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                         in
                                                      let g_sort_is =
                                                        let uu____4679 =
                                                          let uu____4680 =
                                                            let uu____4683 =
                                                              let uu____4684
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4684.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4683
                                                             in
                                                          uu____4680.FStar_Syntax_Syntax.n
                                                           in
                                                        match uu____4679 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____4717 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c
                                                               in
                                                            (match uu____4717
                                                             with
                                                             | (bs1,c1) ->
                                                                 let bs_subst
                                                                   =
                                                                   let uu____4727
                                                                    =
                                                                    let uu____4734
                                                                    =
                                                                    let uu____4735
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____4735
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____4756
                                                                    =
                                                                    let uu____4759
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4759
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____4734,
                                                                    uu____4756)
                                                                     in
                                                                   FStar_Syntax_Syntax.NT
                                                                    uu____4727
                                                                    in
                                                                 let c2 =
                                                                   FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1
                                                                    in
                                                                 let uu____4773
                                                                   =
                                                                   let uu____4776
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2)  in
                                                                   let uu____4777
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed  in
                                                                   let uu____4779
                                                                    =
                                                                    let uu____4781
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2)  in
                                                                    FStar_Util.format1
                                                                    "bind g binder comp type is not a repr (%s)"
                                                                    uu____4781
                                                                     in
                                                                   FStar_Syntax_Util.effect_indices_from_repr
                                                                    uu____4776
                                                                    uu____4777
                                                                    r1
                                                                    uu____4779
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____4773
                                                                   (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst)))
                                                        | uu____4788 ->
                                                            failwith
                                                              "impossible: mk_indexed_bind"
                                                         in
                                                      let env_g =
                                                        FStar_TypeChecker_Env.push_binders
                                                          env [x_a]
                                                         in
                                                      let uu____4805 =
                                                        FStar_List.fold_left2
                                                          (fun g  ->
                                                             fun i1  ->
                                                               fun g_i1  ->
                                                                 (let uu____4823
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "LayeredEffectsRel")
                                                                     in
                                                                  if
                                                                    uu____4823
                                                                  then
                                                                    let uu____4828
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    i1  in
                                                                    let uu____4830
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    g_i1  in
                                                                    FStar_Util.print2
                                                                    "LayeredEffects teq %s = %s\n"
                                                                    uu____4828
                                                                    uu____4830
                                                                  else ());
                                                                 (let uu____4835
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env_g i1
                                                                    g_i1  in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____4835))
                                                          FStar_TypeChecker_Env.trivial_guard
                                                          is2 g_sort_is
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4805
                                                        (FStar_TypeChecker_Env.close_guard
                                                           env [x_a])
                                                       in
                                                    let bind_ct =
                                                      let uu____4849 =
                                                        FStar_All.pipe_right
                                                          bind_c
                                                          (FStar_Syntax_Subst.subst_comp
                                                             subst)
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4849
                                                        FStar_Syntax_Util.comp_to_comp_typ
                                                       in
                                                    let fml =
                                                      let uu____4851 =
                                                        let uu____4856 =
                                                          FStar_List.hd
                                                            bind_ct.FStar_Syntax_Syntax.comp_univs
                                                           in
                                                        let uu____4857 =
                                                          let uu____4858 =
                                                            FStar_List.hd
                                                              bind_ct.FStar_Syntax_Syntax.effect_args
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____4858
                                                           in
                                                        (uu____4856,
                                                          uu____4857)
                                                         in
                                                      match uu____4851 with
                                                      | (u,wp) ->
                                                          FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                            env u
                                                            bind_ct.FStar_Syntax_Syntax.result_typ
                                                            wp
                                                            FStar_Range.dummyRange
                                                       in
                                                    let is =
                                                      let uu____4884 =
                                                        FStar_Syntax_Subst.compress
                                                          bind_ct.FStar_Syntax_Syntax.result_typ
                                                         in
                                                      let uu____4885 =
                                                        FStar_Syntax_Util.is_layered
                                                          p_ed
                                                         in
                                                      let uu____4887 =
                                                        let uu____4889 =
                                                          FStar_Syntax_Print.term_to_string
                                                            bind_ct.FStar_Syntax_Syntax.result_typ
                                                           in
                                                        FStar_Util.format1
                                                          "bind ct result type not a repr (%s)"
                                                          uu____4889
                                                         in
                                                      FStar_Syntax_Util.effect_indices_from_repr
                                                        uu____4884 uu____4885
                                                        r1 uu____4887
                                                       in
                                                    let c =
                                                      let uu____4893 =
                                                        let uu____4894 =
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
                                                            (p_ed.FStar_Syntax_Syntax.mname);
                                                          FStar_Syntax_Syntax.result_typ
                                                            = t2;
                                                          FStar_Syntax_Syntax.effect_args
                                                            = uu____4894;
                                                          FStar_Syntax_Syntax.flags
                                                            = flags
                                                        }  in
                                                      FStar_Syntax_Syntax.mk_Comp
                                                        uu____4893
                                                       in
                                                    ((let uu____4914 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "LayeredEffectsApp")
                                                         in
                                                      if uu____4914
                                                      then
                                                        let uu____4919 =
                                                          FStar_Syntax_Print.comp_to_string
                                                            c
                                                           in
                                                        FStar_Util.print1
                                                          "} c after bind: %s\n"
                                                          uu____4919
                                                      else ());
                                                     (let uu____4924 =
                                                        let uu____4925 =
                                                          let uu____4928 =
                                                            let uu____4931 =
                                                              let uu____4934
                                                                =
                                                                let uu____4937
                                                                  =
                                                                  FStar_TypeChecker_Env.guard_of_guard_formula
                                                                    (
                                                                    FStar_TypeChecker_Common.NonTrivial
                                                                    fml)
                                                                   in
                                                                [uu____4937]
                                                                 in
                                                              g_guard ::
                                                                uu____4934
                                                               in
                                                            f_guard ::
                                                              uu____4931
                                                             in
                                                          g_uvars ::
                                                            uu____4928
                                                           in
                                                        FStar_TypeChecker_Env.conj_guards
                                                          uu____4925
                                                         in
                                                      (c, uu____4924)))))))))
  
let (mk_wp_bind :
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
                let uu____4982 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____5008 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____5008 with
                  | (a,kwp) ->
                      let uu____5039 = destruct_wp_comp ct1  in
                      let uu____5046 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____5039, uu____5046)
                   in
                match uu____4982 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____5099 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____5099]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____5119 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____5119]
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
                      let uu____5166 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____5175 =
                        let uu____5186 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____5195 =
                          let uu____5206 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____5215 =
                            let uu____5226 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____5235 =
                              let uu____5246 =
                                let uu____5255 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____5255  in
                              [uu____5246]  in
                            uu____5226 :: uu____5235  in
                          uu____5206 :: uu____5215  in
                        uu____5186 :: uu____5195  in
                      uu____5166 :: uu____5175  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____5308 =
                        let uu____5313 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_t1; u_t2] env md bind_wp
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5313 wp_args  in
                      uu____5308 FStar_Pervasives_Native.None
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
              let uu____5361 =
                let uu____5366 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
                let uu____5367 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
                (uu____5366, uu____5367)  in
              match uu____5361 with
              | (ct1,ct2) ->
                  let uu____5374 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name
                     in
                  (match uu____5374 with
                   | FStar_Pervasives_Native.Some (p,f_bind) ->
                       ((let uu____5416 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "LayeredEffectsApp")
                            in
                         if uu____5416
                         then
                           let uu____5421 =
                             FStar_Ident.string_of_lid
                               ct1.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____5423 =
                             FStar_Ident.string_of_lid
                               ct2.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____5425 = FStar_Ident.string_of_lid p  in
                           FStar_Util.print3
                             "Found a polymonadic bind (%s, %s) |> %s, using it\n"
                             uu____5421 uu____5423 uu____5425
                         else ());
                        f_bind env ct1 b ct2 flags r1)
                   | FStar_Pervasives_Native.None  ->
                       let uu____5440 = lift_comps env c1 c2 b Lift_for_bind
                          in
                       (match uu____5440 with
                        | (m,c11,c21,g_lift) ->
                            let uu____5457 =
                              let uu____5462 =
                                FStar_Syntax_Util.comp_to_comp_typ c11  in
                              let uu____5463 =
                                FStar_Syntax_Util.comp_to_comp_typ c21  in
                              (uu____5462, uu____5463)  in
                            (match uu____5457 with
                             | (ct11,ct21) ->
                                 let uu____5470 =
                                   let uu____5475 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m
                                      in
                                   if uu____5475
                                   then
                                     let bind_t =
                                       let uu____5483 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env)
                                          in
                                       FStar_All.pipe_right uu____5483
                                         FStar_Syntax_Util.get_bind_vc_combinator
                                        in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu____5486 =
                                        mk_wp_bind env m ct11 b ct21 flags r1
                                         in
                                      (uu____5486,
                                        FStar_TypeChecker_Env.trivial_guard))
                                    in
                                 (match uu____5470 with
                                  | (c,g_bind) ->
                                      let uu____5493 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind
                                         in
                                      (c, uu____5493)))))
  
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
            let uu____5529 =
              let uu____5530 =
                let uu____5541 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____5541]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____5530;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____5529  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____5586 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_5592  ->
              match uu___1_5592 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5595 -> false))
       in
    if uu____5586
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_5607  ->
              match uu___2_5607 with
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
        let uu____5635 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5635
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____5646 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____5646  in
           let pure_assume_wp1 =
             let uu____5651 = FStar_TypeChecker_Env.get_range env  in
             let uu____5652 =
               let uu____5657 =
                 let uu____5658 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____5658]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____5657  in
             uu____5652 FStar_Pervasives_Native.None uu____5651  in
           let uu____5691 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____5691)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5719 =
          let uu____5720 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5720 with
          | (c,g_c) ->
              let uu____5731 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5731
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5745 = weaken_comp env c f1  in
                     (match uu____5745 with
                      | (c1,g_w) ->
                          let uu____5756 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____5756)))
           in
        let uu____5757 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5757 weaken
  
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
                 let uu____5814 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____5814  in
               let pure_assert_wp1 =
                 let uu____5819 =
                   let uu____5824 =
                     let uu____5825 =
                       let uu____5834 = label_opt env reason r f  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                         uu____5834
                        in
                     [uu____5825]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____5824
                    in
                 uu____5819 FStar_Pervasives_Native.None r  in
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
            let uu____5904 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____5904
            then (lc, g0)
            else
              (let flags =
                 let uu____5916 =
                   let uu____5924 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____5924
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5916 with
                 | (maybe_trivial_post,flags) ->
                     let uu____5954 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_5962  ->
                               match uu___3_5962 with
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
                               | uu____5965 -> []))
                        in
                     FStar_List.append flags uu____5954
                  in
               let strengthen uu____5975 =
                 let uu____5976 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____5976 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____5995 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____5995 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____6002 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____6002
                              then
                                let uu____6006 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____6008 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____6006 uu____6008
                              else ());
                             (let uu____6013 =
                                strengthen_comp env reason c f flags  in
                              match uu____6013 with
                              | (c1,g_s) ->
                                  let uu____6024 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____6024))))
                  in
               let uu____6025 =
                 let uu____6026 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____6026
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____6025,
                 (let uu___695_6028 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___695_6028.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___695_6028.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___695_6028.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_6037  ->
            match uu___4_6037 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____6041 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____6070 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____6070
          then e
          else
            (let uu____6077 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____6080 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____6080)
                in
             if uu____6077
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
              let is_unit =
                match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.unit_lid
                | uu____6150 -> false  in
              if is_unit
              then
                let uu____6157 =
                  let uu____6159 =
                    let uu____6160 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____6160
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____6159
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____6157
                 then
                   let uu____6169 = FStar_Syntax_Subst.open_term_bv b phi  in
                   match uu____6169 with
                   | (b1,phi1) ->
                       let phi2 =
                         FStar_Syntax_Subst.subst
                           [FStar_Syntax_Syntax.NT
                              (b1, FStar_Syntax_Syntax.unit_const)] phi1
                          in
                       weaken_comp env c phi2
                 else
                   (let uu____6185 = close_wp_comp env [x] c  in
                    (uu____6185, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____6188 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
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
          fun uu____6216  ->
            match uu____6216 with
            | (b,lc2) ->
                let debug f =
                  let uu____6236 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____6236 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____6249 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____6249
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____6259 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____6259
                       then
                         let uu____6264 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____6264
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____6271 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____6271
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____6280 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____6280
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____6287 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____6287
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____6303 =
                  let uu____6304 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____6304
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____6312 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____6312, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____6315 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____6315 with
                     | (c1,g_c1) ->
                         let uu____6326 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____6326 with
                          | (c2,g_c2) ->
                              let trivial_guard =
                                let uu____6338 =
                                  match b with
                                  | FStar_Pervasives_Native.Some x ->
                                      let b1 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      let uu____6341 =
                                        FStar_Syntax_Syntax.is_null_binder b1
                                         in
                                      if uu____6341
                                      then g_c2
                                      else
                                        FStar_TypeChecker_Env.close_guard env
                                          [b1] g_c2
                                  | FStar_Pervasives_Native.None  -> g_c2  in
                                FStar_TypeChecker_Env.conj_guard g_c1
                                  uu____6338
                                 in
                              (debug
                                 (fun uu____6367  ->
                                    let uu____6368 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____6370 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____6375 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____6368 uu____6370 uu____6375);
                               (let aux uu____6393 =
                                  let uu____6394 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____6394
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____6425
                                        ->
                                        let uu____6426 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____6426
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____6458 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____6458
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____6505 =
                                  let aux_with_trivial_guard uu____6535 =
                                    let uu____6536 = aux ()  in
                                    match uu____6536 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c, trivial_guard, reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____6594 =
                                    let uu____6596 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____6596  in
                                  if uu____6594
                                  then
                                    let uu____6612 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____6612
                                     then
                                       FStar_Util.Inl
                                         (c2, trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____6639 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____6639))
                                  else
                                    (let uu____6656 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____6656
                                     then
                                       let close_with_type_of_x x c =
                                         let x1 =
                                           let uu___798_6687 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___798_6687.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___798_6687.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           }  in
                                         maybe_capture_unit_refinement env
                                           x1.FStar_Syntax_Syntax.sort x1 c
                                          in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some
                                          e,FStar_Pervasives_Native.Some x)
                                           ->
                                           let uu____6718 =
                                             let uu____6723 =
                                               FStar_All.pipe_right c2
                                                 (FStar_Syntax_Subst.subst_comp
                                                    [FStar_Syntax_Syntax.NT
                                                       (x, e)])
                                                in
                                             FStar_All.pipe_right uu____6723
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6718 with
                                            | (c21,g_close) ->
                                                let uu____6744 =
                                                  let uu____6752 =
                                                    let uu____6753 =
                                                      let uu____6756 =
                                                        let uu____6759 =
                                                          FStar_TypeChecker_Env.map_guard
                                                            g_c2
                                                            (FStar_Syntax_Subst.subst
                                                               [FStar_Syntax_Syntax.NT
                                                                  (x, e)])
                                                           in
                                                        [uu____6759; g_close]
                                                         in
                                                      g_c1 :: uu____6756  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6753
                                                     in
                                                  (c21, uu____6752, "c1 Tot")
                                                   in
                                                FStar_Util.Inl uu____6744)
                                       | (uu____6772,FStar_Pervasives_Native.Some
                                          x) ->
                                           let uu____6784 =
                                             FStar_All.pipe_right c2
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6784 with
                                            | (c21,g_close) ->
                                                let uu____6807 =
                                                  let uu____6815 =
                                                    let uu____6816 =
                                                      let uu____6819 =
                                                        let uu____6822 =
                                                          let uu____6823 =
                                                            let uu____6824 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____6824]  in
                                                          FStar_TypeChecker_Env.close_guard
                                                            env uu____6823
                                                            g_c2
                                                           in
                                                        [uu____6822; g_close]
                                                         in
                                                      g_c1 :: uu____6819  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6816
                                                     in
                                                  (c21, uu____6815,
                                                    "c1 Tot only close")
                                                   in
                                                FStar_Util.Inl uu____6807)
                                       | (uu____6853,uu____6854) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____6869 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____6869
                                        then
                                          let uu____6884 =
                                            let uu____6892 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____6892, trivial_guard,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____6884
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____6905 = try_simplify ()  in
                                match uu____6905 with
                                | FStar_Util.Inl (c,g,reason) ->
                                    (debug
                                       (fun uu____6940  ->
                                          let uu____6941 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____6941);
                                     (c, g))
                                | FStar_Util.Inr reason ->
                                    (debug
                                       (fun uu____6957  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 g =
                                        let uu____6988 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____6988 with
                                        | (c,g_bind) ->
                                            let uu____6999 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g g_bind
                                               in
                                            (c, uu____6999)
                                         in
                                      let mk_seq c11 b1 c21 =
                                        let c12 =
                                          FStar_TypeChecker_Env.unfold_effect_abbrev
                                            env c11
                                           in
                                        let c22 =
                                          FStar_TypeChecker_Env.unfold_effect_abbrev
                                            env c21
                                           in
                                        let uu____7026 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____7026 with
                                        | (m,uu____7038,lift2) ->
                                            let uu____7040 =
                                              lift_comp env c22 lift2  in
                                            (match uu____7040 with
                                             | (c23,g2) ->
                                                 let uu____7051 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____7051 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let trivial =
                                                        let uu____7067 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7067
                                                          FStar_Util.must
                                                         in
                                                      let vc1 =
                                                        let uu____7077 =
                                                          let uu____7082 =
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              trivial
                                                             in
                                                          let uu____7083 =
                                                            let uu____7084 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____7093 =
                                                              let uu____7104
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____7104]
                                                               in
                                                            uu____7084 ::
                                                              uu____7093
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7082
                                                            uu____7083
                                                           in
                                                        uu____7077
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____7137 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____7137 with
                                                       | (c,g_s) ->
                                                           let uu____7152 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____7152))))
                                         in
                                      let uu____7153 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____7169 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____7169, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____7153 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____7185 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____7185
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____7194 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____7194
                                             then
                                               (debug
                                                  (fun uu____7208  ->
                                                     let uu____7209 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____7211 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____7209 uu____7211);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 let g =
                                                   let uu____7218 =
                                                     FStar_TypeChecker_Env.map_guard
                                                       g_c2
                                                       (FStar_Syntax_Subst.subst
                                                          [FStar_Syntax_Syntax.NT
                                                             (x, e1)])
                                                      in
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 uu____7218
                                                    in
                                                 mk_bind1 c1 b c21 g))
                                             else
                                               (let uu____7223 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____7226 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____7226)
                                                   in
                                                if uu____7223
                                                then
                                                  let e1' =
                                                    let uu____7251 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____7251
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug
                                                     (fun uu____7263  ->
                                                        let uu____7264 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____7266 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____7264
                                                          uu____7266);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug
                                                     (fun uu____7281  ->
                                                        let uu____7282 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____7284 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____7282
                                                          uu____7284);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____7291 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____7291
                                                       in
                                                    let uu____7292 =
                                                      let uu____7297 =
                                                        let uu____7298 =
                                                          let uu____7299 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____7299]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____7298
                                                         in
                                                      weaken_comp uu____7297
                                                        c21 x_eq_e
                                                       in
                                                    match uu____7292 with
                                                    | (c22,g_w) ->
                                                        let g =
                                                          let uu____7325 =
                                                            let uu____7326 =
                                                              let uu____7327
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x
                                                                 in
                                                              [uu____7327]
                                                               in
                                                            let uu____7346 =
                                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                                g_c2 x_eq_e
                                                               in
                                                            FStar_TypeChecker_Env.close_guard
                                                              env uu____7326
                                                              uu____7346
                                                             in
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g_c1 uu____7325
                                                           in
                                                        let uu____7347 =
                                                          mk_bind1 c1 b c22 g
                                                           in
                                                        (match uu____7347
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____7358 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____7358))))))
                                          else mk_bind1 c1 b c2 trivial_guard))))))
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
      | uu____7375 -> g2
  
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
            (let uu____7399 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____7399)
           in
        let flags =
          if should_return1
          then
            let uu____7407 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____7407
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine uu____7425 =
          let uu____7426 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____7426 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____7439 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____7439
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____7447 =
                  let uu____7449 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____7449  in
                (if uu____7447
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___923_7458 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___923_7458.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___923_7458.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___923_7458.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____7459 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____7459, g_c)
                 else
                   (let uu____7462 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____7462, g_c)))
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
                 let ret =
                   let uu____7473 =
                     let uu____7474 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____7474
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____7473
                    in
                 let eq = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret
                     (FStar_TypeChecker_Common.NonTrivial eq)
                    in
                 let uu____7477 =
                   let uu____7482 =
                     let uu____7483 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____7483
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____7482  in
                 match uu____7477 with
                 | (bind_c,g_bind) ->
                     let uu____7492 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____7493 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____7492, uu____7493))
           in
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
  fun r  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun e2  ->
            fun uu____7529  ->
              match uu____7529 with
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
                    let uu____7541 =
                      ((let uu____7545 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____7545) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____7541
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____7563 =
        let uu____7564 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____7564  in
      FStar_Syntax_Syntax.fvar uu____7563 FStar_Syntax_Syntax.delta_constant
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
                  let uu____7614 =
                    let uu____7619 =
                      let uu____7620 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____7620 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7619 [u_a]
                     in
                  match uu____7614 with
                  | (uu____7631,conjunction) ->
                      let uu____7633 =
                        let uu____7642 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____7657 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____7642, uu____7657)  in
                      (match uu____7633 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____7703 =
                               let uu____7705 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____7705 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7703)
                              in
                           let uu____7709 =
                             let uu____7754 =
                               let uu____7755 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____7755.FStar_Syntax_Syntax.n  in
                             match uu____7754 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____7804) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____7836 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____7836 with
                                  | (a_b::bs1,body1) ->
                                      let uu____7908 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____7908 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____8056 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____8056)))
                             | uu____8089 ->
                                 let uu____8090 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____8090 r
                              in
                           (match uu____7709 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____8215 =
                                  let uu____8222 =
                                    let uu____8223 =
                                      let uu____8224 =
                                        let uu____8231 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____8231, a)  in
                                      FStar_Syntax_Syntax.NT uu____8224  in
                                    [uu____8223]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____8222
                                    (fun b  ->
                                       let uu____8247 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____8249 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____8251 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____8247 uu____8249 uu____8251) r
                                   in
                                (match uu____8215 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____8289 =
                                                let uu____8296 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____8296, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____8289) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____8335 =
                                           let uu____8336 =
                                             let uu____8339 =
                                               let uu____8340 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8340.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8339
                                              in
                                           uu____8336.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8335 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8351,uu____8352::is) ->
                                             let uu____8394 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8394
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8427 ->
                                             let uu____8428 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8428 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____8444 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8444)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____8449 =
                                           let uu____8450 =
                                             let uu____8453 =
                                               let uu____8454 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8454.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8453
                                              in
                                           uu____8450.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8449 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8465,uu____8466::is) ->
                                             let uu____8508 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8508
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8541 ->
                                             let uu____8542 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8542 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____8558 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8558)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____8563 =
                                         let uu____8564 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____8564.FStar_Syntax_Syntax.n  in
                                       match uu____8563 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8569,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8624 ->
                                           let uu____8625 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____8625 r
                                        in
                                     let uu____8634 =
                                       let uu____8635 =
                                         let uu____8636 =
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
                                             uu____8636;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____8635
                                        in
                                     let uu____8659 =
                                       let uu____8660 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8660 g_guard
                                        in
                                     (uu____8634, uu____8659))))
  
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
                fun uu____8705  ->
                  let if_then_else =
                    let uu____8711 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____8711 FStar_Util.must  in
                  let uu____8718 = destruct_wp_comp ct1  in
                  match uu____8718 with
                  | (uu____8729,uu____8730,wp_t) ->
                      let uu____8732 = destruct_wp_comp ct2  in
                      (match uu____8732 with
                       | (uu____8743,uu____8744,wp_e) ->
                           let wp =
                             let uu____8749 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             let uu____8750 =
                               let uu____8755 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_a] env ed if_then_else
                                  in
                               let uu____8756 =
                                 let uu____8757 =
                                   FStar_Syntax_Syntax.as_arg a  in
                                 let uu____8766 =
                                   let uu____8777 =
                                     FStar_Syntax_Syntax.as_arg p  in
                                   let uu____8786 =
                                     let uu____8797 =
                                       FStar_Syntax_Syntax.as_arg wp_t  in
                                     let uu____8806 =
                                       let uu____8817 =
                                         FStar_Syntax_Syntax.as_arg wp_e  in
                                       [uu____8817]  in
                                     uu____8797 :: uu____8806  in
                                   uu____8777 :: uu____8786  in
                                 uu____8757 :: uu____8766  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____8755
                                 uu____8756
                                in
                             uu____8750 FStar_Pervasives_Native.None
                               uu____8749
                              in
                           let uu____8866 = mk_comp ed u_a a wp []  in
                           (uu____8866, FStar_TypeChecker_Env.trivial_guard))
  
let (bind_cases :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ * FStar_Ident.lident *
        FStar_Syntax_Syntax.cflag Prims.list *
        (Prims.bool -> FStar_TypeChecker_Common.lcomp)) Prims.list ->
        FStar_Syntax_Syntax.bv -> FStar_TypeChecker_Common.lcomp)
  =
  fun env0  ->
    fun res_t  ->
      fun lcases  ->
        fun scrutinee  ->
          let env =
            let uu____8920 =
              let uu____8921 =
                FStar_All.pipe_right scrutinee FStar_Syntax_Syntax.mk_binder
                 in
              [uu____8921]  in
            FStar_TypeChecker_Env.push_binders env0 uu____8920  in
          let eff =
            FStar_List.fold_left
              (fun eff  ->
                 fun uu____8968  ->
                   match uu____8968 with
                   | (uu____8982,eff_label,uu____8984,uu____8985) ->
                       join_effects env eff eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases
             in
          let uu____8998 =
            let uu____9006 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu____9044  ->
                      match uu____9044 with
                      | (uu____9059,uu____9060,flags,uu____9062) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___5_9079  ->
                                  match uu___5_9079 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                      true
                                  | uu____9082 -> false))))
               in
            if uu____9006
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, [])  in
          match uu____8998 with
          | (should_not_inline_whole_match,bind_cases_flags) ->
              let bind_cases uu____9119 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                   in
                let uu____9121 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                   in
                if uu____9121
                then
                  let uu____9128 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                     in
                  (uu____9128, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let default_case =
                     let post_k =
                       let uu____9135 =
                         let uu____9144 =
                           FStar_Syntax_Syntax.null_binder res_t  in
                         [uu____9144]  in
                       let uu____9163 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9135 uu____9163  in
                     let kwp =
                       let uu____9169 =
                         let uu____9178 =
                           FStar_Syntax_Syntax.null_binder post_k  in
                         [uu____9178]  in
                       let uu____9197 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9169 uu____9197  in
                     let post =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None post_k
                        in
                     let wp =
                       let uu____9204 =
                         let uu____9205 = FStar_Syntax_Syntax.mk_binder post
                            in
                         [uu____9205]  in
                       let uu____9224 =
                         let uu____9227 =
                           let uu____9234 =
                             FStar_TypeChecker_Env.get_range env  in
                           label FStar_TypeChecker_Err.exhaustiveness_check
                             uu____9234
                            in
                         let uu____9235 =
                           fvar_const env FStar_Parser_Const.false_lid  in
                         FStar_All.pipe_left uu____9227 uu____9235  in
                       FStar_Syntax_Util.abs uu____9204 uu____9224
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
                     let uu____9259 =
                       should_not_inline_whole_match ||
                         (let uu____9262 = is_pure_or_ghost_effect env eff
                             in
                          Prims.op_Negation uu____9262)
                        in
                     if uu____9259 then cthen true else cthen false  in
                   let branch_conditions =
                     let uu____9274 =
                       let uu____9287 =
                         let uu____9292 =
                           let uu____9303 =
                             FStar_All.pipe_right lcases
                               (FStar_List.map
                                  (fun uu____9347  ->
                                     match uu____9347 with
                                     | (g,uu____9362,uu____9363,uu____9364)
                                         -> g))
                              in
                           FStar_All.pipe_right uu____9303
                             (FStar_List.fold_left
                                (fun uu____9408  ->
                                   fun g  ->
                                     match uu____9408 with
                                     | (conds,acc) ->
                                         let cond =
                                           let uu____9449 =
                                             FStar_Syntax_Util.mk_neg g  in
                                           FStar_Syntax_Util.mk_conj acc
                                             uu____9449
                                            in
                                         ((FStar_List.append conds [cond]),
                                           cond))
                                ([FStar_Syntax_Util.t_true],
                                  FStar_Syntax_Util.t_true))
                            in
                         FStar_All.pipe_right uu____9292
                           FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____9287
                         (FStar_List.splitAt (FStar_List.length lcases))
                        in
                     FStar_All.pipe_right uu____9274
                       FStar_Pervasives_Native.fst
                      in
                   let uu____9550 =
                     FStar_List.fold_right2
                       (fun uu____9613  ->
                          fun bcond  ->
                            fun uu____9615  ->
                              match (uu____9613, uu____9615) with
                              | ((g,eff_label,uu____9675,cthen),(uu____9677,celse,g_comp))
                                  ->
                                  let uu____9724 =
                                    let uu____9729 =
                                      maybe_return eff_label cthen  in
                                    FStar_TypeChecker_Common.lcomp_comp
                                      uu____9729
                                     in
                                  (match uu____9724 with
                                   | (cthen1,gthen) ->
                                       let gthen1 =
                                         let uu____9741 =
                                           FStar_Syntax_Util.mk_conj bcond g
                                            in
                                         FStar_TypeChecker_Common.weaken_guard_formula
                                           gthen uu____9741
                                          in
                                       let uu____9742 =
                                         let uu____9753 =
                                           lift_comps_sep_guards env cthen1
                                             celse
                                             FStar_Pervasives_Native.None
                                             Lift_for_match
                                            in
                                         match uu____9753 with
                                         | (m,cthen2,celse1,g_lift_then,g_lift_else)
                                             ->
                                             let md =
                                               FStar_TypeChecker_Env.get_effect_decl
                                                 env m
                                                in
                                             let uu____9780 =
                                               FStar_All.pipe_right cthen2
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                in
                                             let uu____9781 =
                                               FStar_All.pipe_right celse1
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                in
                                             (md, uu____9780, uu____9781,
                                               g_lift_then, g_lift_else)
                                          in
                                       (match uu____9742 with
                                        | (md,ct_then,ct_else,g_lift_then,g_lift_else)
                                            ->
                                            let fn =
                                              let uu____9832 =
                                                FStar_All.pipe_right md
                                                  FStar_Syntax_Util.is_layered
                                                 in
                                              if uu____9832
                                              then mk_layered_conjunction
                                              else mk_non_layered_conjunction
                                               in
                                            let g_lift_then1 =
                                              let uu____9867 =
                                                FStar_Syntax_Util.mk_conj
                                                  bcond g
                                                 in
                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                g_lift_then uu____9867
                                               in
                                            let g_lift_else1 =
                                              let uu____9869 =
                                                let uu____9870 =
                                                  FStar_Syntax_Util.mk_neg g
                                                   in
                                                FStar_Syntax_Util.mk_conj
                                                  bcond uu____9870
                                                 in
                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                g_lift_else uu____9869
                                               in
                                            let g_lift =
                                              FStar_TypeChecker_Env.conj_guard
                                                g_lift_then1 g_lift_else1
                                               in
                                            let uu____9874 =
                                              let uu____9879 =
                                                FStar_TypeChecker_Env.get_range
                                                  env
                                                 in
                                              fn env md u_res_t res_t g
                                                ct_then ct_else uu____9879
                                               in
                                            (match uu____9874 with
                                             | (c,g_conjunction) ->
                                                 let uu____9890 =
                                                   FStar_TypeChecker_Env.conj_guards
                                                     [g_comp;
                                                     gthen1;
                                                     g_lift;
                                                     g_conjunction]
                                                    in
                                                 ((FStar_Pervasives_Native.Some
                                                     md), c, uu____9890)))))
                       lcases branch_conditions
                       (FStar_Pervasives_Native.None, default_case,
                         FStar_TypeChecker_Env.trivial_guard)
                      in
                   match uu____9550 with
                   | (md,comp,g_comp) ->
                       let g_comp1 =
                         let uu____9907 =
                           let uu____9908 =
                             FStar_All.pipe_right scrutinee
                               FStar_Syntax_Syntax.mk_binder
                              in
                           [uu____9908]  in
                         FStar_TypeChecker_Env.close_guard env0 uu____9907
                           g_comp
                          in
                       (match lcases with
                        | [] -> (comp, g_comp1)
                        | uu____9951::[] -> (comp, g_comp1)
                        | uu____9994 ->
                            let uu____10011 =
                              let uu____10013 =
                                FStar_All.pipe_right md FStar_Util.must  in
                              FStar_All.pipe_right uu____10013
                                FStar_Syntax_Util.is_layered
                               in
                            if uu____10011
                            then (comp, g_comp1)
                            else
                              (let comp1 =
                                 FStar_TypeChecker_Env.comp_to_comp_typ env
                                   comp
                                  in
                               let md1 =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   comp1.FStar_Syntax_Syntax.effect_name
                                  in
                               let uu____10026 = destruct_wp_comp comp1  in
                               match uu____10026 with
                               | (uu____10037,uu____10038,wp) ->
                                   let ite_wp =
                                     let uu____10041 =
                                       FStar_All.pipe_right md1
                                         FStar_Syntax_Util.get_wp_ite_combinator
                                        in
                                     FStar_All.pipe_right uu____10041
                                       FStar_Util.must
                                      in
                                   let wp1 =
                                     let uu____10051 =
                                       let uu____10056 =
                                         FStar_TypeChecker_Env.inst_effect_fun_with
                                           [u_res_t] env md1 ite_wp
                                          in
                                       let uu____10057 =
                                         let uu____10058 =
                                           FStar_Syntax_Syntax.as_arg res_t
                                            in
                                         let uu____10067 =
                                           let uu____10078 =
                                             FStar_Syntax_Syntax.as_arg wp
                                              in
                                           [uu____10078]  in
                                         uu____10058 :: uu____10067  in
                                       FStar_Syntax_Syntax.mk_Tm_app
                                         uu____10056 uu____10057
                                        in
                                     uu____10051 FStar_Pervasives_Native.None
                                       wp.FStar_Syntax_Syntax.pos
                                      in
                                   let uu____10111 =
                                     mk_comp md1 u_res_t res_t wp1
                                       bind_cases_flags
                                      in
                                   (uu____10111, g_comp1))))
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
          let uu____10146 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____10146 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____10162 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____10168 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____10162 uu____10168
              else
                (let uu____10177 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____10183 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____10177 uu____10183)
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
          let uu____10208 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____10208
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____10211 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____10211
        then u_res
        else
          (let is_total =
             let uu____10218 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____10218
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____10229 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____10229 with
              | FStar_Pervasives_Native.None  ->
                  let uu____10232 =
                    let uu____10238 =
                      let uu____10240 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____10240
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____10238)
                     in
                  FStar_Errors.raise_error uu____10232
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
      let uu____10264 = destruct_wp_comp ct  in
      match uu____10264 with
      | (u_t,t,wp) ->
          let vc =
            let uu____10283 = FStar_TypeChecker_Env.get_range env  in
            let uu____10284 =
              let uu____10289 =
                let uu____10290 =
                  let uu____10291 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_trivial_combinator
                     in
                  FStar_All.pipe_right uu____10291 FStar_Util.must  in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____10290
                 in
              let uu____10298 =
                let uu____10299 = FStar_Syntax_Syntax.as_arg t  in
                let uu____10308 =
                  let uu____10319 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____10319]  in
                uu____10299 :: uu____10308  in
              FStar_Syntax_Syntax.mk_Tm_app uu____10289 uu____10298  in
            uu____10284 FStar_Pervasives_Native.None uu____10283  in
          let uu____10352 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____10352)
  
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
                  let uu____10407 =
                    FStar_TypeChecker_Env.try_lookup_lid env f  in
                  match uu____10407 with
                  | FStar_Pervasives_Native.Some uu____10422 ->
                      ((let uu____10440 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____10440
                        then
                          let uu____10444 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____10444
                        else ());
                       (let coercion =
                          let uu____10450 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____10450
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____10457 =
                            let uu____10458 =
                              let uu____10459 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10459
                               in
                            (FStar_Pervasives_Native.None, uu____10458)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____10457
                           in
                        let e1 =
                          let uu____10465 =
                            let uu____10470 =
                              let uu____10471 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____10471]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____10470
                             in
                          uu____10465 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____10505 =
                          let uu____10511 =
                            let uu____10513 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____10513
                             in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____10511)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____10505);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____10532 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10550 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10561 -> false 
let rec (check_erased :
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
          FStar_TypeChecker_Env.HNF;
          FStar_TypeChecker_Env.Iota]
         in
      let t1 = norm' env t  in
      let t2 = FStar_Syntax_Util.unrefine t1  in
      let uu____10585 = FStar_Syntax_Util.head_and_args t2  in
      match uu____10585 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____10630 =
              let uu____10645 =
                let uu____10646 = FStar_Syntax_Subst.compress h1  in
                uu____10646.FStar_Syntax_Syntax.n  in
              (uu____10645, args)  in
            match uu____10630 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____10693,uu____10694) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____10727) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match
               (uu____10748,branches),uu____10750) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc  ->
                        fun br  ->
                          match acc with
                          | Yes uu____10814 -> Maybe
                          | Maybe  -> Maybe
                          | No  ->
                              let uu____10815 =
                                FStar_Syntax_Subst.open_branch br  in
                              (match uu____10815 with
                               | (uu____10816,uu____10817,br_body) ->
                                   let uu____10835 =
                                     let uu____10836 =
                                       let uu____10841 =
                                         let uu____10842 =
                                           let uu____10845 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names
                                              in
                                           FStar_All.pipe_right uu____10845
                                             FStar_Util.set_elements
                                            in
                                         FStar_All.pipe_right uu____10842
                                           (FStar_TypeChecker_Env.push_bvs
                                              env)
                                          in
                                       check_erased uu____10841  in
                                     FStar_All.pipe_right br_body uu____10836
                                      in
                                   (match uu____10835 with
                                    | No  -> No
                                    | uu____10856 -> Maybe))) No)
            | uu____10857 -> No  in
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
            (((let uu____10909 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____10909) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____10928 =
                 let uu____10929 = FStar_Syntax_Subst.compress t1  in
                 uu____10929.FStar_Syntax_Syntax.n  in
               match uu____10928 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____10934 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____10944 =
                 let uu____10945 = FStar_Syntax_Subst.compress t1  in
                 uu____10945.FStar_Syntax_Syntax.n  in
               match uu____10944 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____10950 -> false  in
             let is_type t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let t2 = FStar_Syntax_Util.unrefine t1  in
               let uu____10961 =
                 let uu____10962 = FStar_Syntax_Subst.compress t2  in
                 uu____10962.FStar_Syntax_Syntax.n  in
               match uu____10961 with
               | FStar_Syntax_Syntax.Tm_type uu____10966 -> true
               | uu____10968 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____10971 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____10971 with
             | (head,args) ->
                 ((let uu____11021 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____11021
                   then
                     let uu____11025 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____11027 = FStar_Syntax_Print.term_to_string e
                        in
                     let uu____11029 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____11031 =
                       FStar_Syntax_Print.term_to_string exp_t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____11025 uu____11027 uu____11029 uu____11031
                   else ());
                  (let mk_erased u t =
                     let uu____11049 =
                       let uu____11052 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____11052 [u]  in
                     let uu____11053 =
                       let uu____11064 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____11064]  in
                     FStar_Syntax_Util.mk_app uu____11049 uu____11053  in
                   let uu____11089 =
                     let uu____11104 =
                       let uu____11105 = FStar_Syntax_Util.un_uinst head  in
                       uu____11105.FStar_Syntax_Syntax.n  in
                     (uu____11104, args)  in
                   match uu____11089 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type exp_t)
                       ->
                       let uu____11143 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____11143 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____11183 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11183 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11223 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11223 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11263 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11263 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____11284 ->
                       let uu____11299 =
                         let uu____11304 = check_erased env res_typ  in
                         let uu____11305 = check_erased env exp_t  in
                         (uu____11304, uu____11305)  in
                       (match uu____11299 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11314 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____11314 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____11325 =
                                   let uu____11330 =
                                     let uu____11331 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____11331]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____11330
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____11325 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11366 =
                              let uu____11371 =
                                let uu____11372 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____11372]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____11371
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____11366 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____11405 ->
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
        let uu____11440 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____11440 with
        | (hd,args) ->
            let uu____11489 =
              let uu____11504 =
                let uu____11505 = FStar_Syntax_Subst.compress hd  in
                uu____11505.FStar_Syntax_Syntax.n  in
              (uu____11504, args)  in
            (match uu____11489 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____11543 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun uu____11570  ->
                      FStar_Pervasives_Native.Some uu____11570) uu____11543
             | uu____11571 -> FStar_Pervasives_Native.None)
  
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
          (let uu____11624 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____11624
           then
             let uu____11627 = FStar_Syntax_Print.term_to_string e  in
             let uu____11629 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____11631 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____11627 uu____11629 uu____11631
           else ());
          (let use_eq =
             (env.FStar_TypeChecker_Env.use_eq_strict ||
                env.FStar_TypeChecker_Env.use_eq)
               ||
               (let uu____11641 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____11641 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____11666 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____11692 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____11692, false)
             else
               (let uu____11702 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____11702, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____11715) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____11727 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____11727
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1365_11743 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1365_11743.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1365_11743.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1365_11743.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard) ->
               let uu____11750 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____11750 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____11766 =
                      let uu____11767 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____11767 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____11787 =
                            let uu____11789 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____11789 = FStar_Syntax_Util.Equal  in
                          if uu____11787
                          then
                            ((let uu____11796 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____11796
                              then
                                let uu____11800 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____11802 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____11800 uu____11802
                              else ());
                             (let uu____11807 = set_result_typ c  in
                              (uu____11807, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____11814 ->
                                   true
                               | uu____11822 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____11831 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____11831
                                  in
                               let lc1 =
                                 let uu____11833 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____11834 =
                                   let uu____11835 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____11835)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____11833 uu____11834
                                  in
                               ((let uu____11839 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____11839
                                 then
                                   let uu____11843 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____11845 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____11847 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____11849 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____11843 uu____11845 uu____11847
                                     uu____11849
                                 else ());
                                (let uu____11854 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____11854 with
                                 | (c1,g_lc) ->
                                     let uu____11865 = set_result_typ c1  in
                                     let uu____11866 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____11865, uu____11866)))
                             else
                               ((let uu____11870 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____11870
                                 then
                                   let uu____11874 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____11876 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____11874 uu____11876
                                 else ());
                                (let uu____11881 = set_result_typ c  in
                                 (uu____11881, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1402_11885 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1402_11885.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1402_11885.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1402_11885.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____11895 =
                      let uu____11896 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____11896
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____11906 =
                           let uu____11907 = FStar_Syntax_Subst.compress f1
                              in
                           uu____11907.FStar_Syntax_Syntax.n  in
                         match uu____11906 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____11914,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____11916;
                                            FStar_Syntax_Syntax.vars =
                                              uu____11917;_},uu____11918)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1418_11944 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1418_11944.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1418_11944.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1418_11944.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____11945 ->
                             let uu____11946 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____11946 with
                              | (c,g_c) ->
                                  ((let uu____11958 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____11958
                                    then
                                      let uu____11962 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____11964 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____11966 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____11968 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____11962 uu____11964 uu____11966
                                        uu____11968
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
                                      if apply_guard
                                      then
                                        let uu____11981 =
                                          let uu____11986 =
                                            let uu____11987 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____11987]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____11986
                                           in
                                        uu____11981
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____12014 =
                                      let uu____12019 =
                                        FStar_All.pipe_left
                                          (fun uu____12040  ->
                                             FStar_Pervasives_Native.Some
                                               uu____12040)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____12041 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____12042 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____12043 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____12019
                                        uu____12041 e uu____12042 uu____12043
                                       in
                                    match uu____12014 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1436_12051 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1436_12051.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1436_12051.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____12053 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____12053
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____12056 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____12056 with
                                         | (c2,g_lc) ->
                                             ((let uu____12068 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____12068
                                               then
                                                 let uu____12072 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____12072
                                               else ());
                                              (let uu____12077 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____12077))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_12086  ->
                              match uu___6_12086 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____12089 -> []))
                       in
                    let lc1 =
                      let uu____12091 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____12091 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1452_12093 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1452_12093.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1452_12093.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1452_12093.FStar_TypeChecker_Common.implicits)
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
        let uu____12129 =
          let uu____12132 =
            let uu____12137 =
              let uu____12138 =
                let uu____12147 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____12147  in
              [uu____12138]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____12137  in
          uu____12132 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____12129  in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____12170 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____12170
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____12189 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____12205 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____12222 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____12222
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____12238)::(ens,uu____12240)::uu____12241 ->
                    let uu____12284 =
                      let uu____12287 = norm req  in
                      FStar_Pervasives_Native.Some uu____12287  in
                    let uu____12288 =
                      let uu____12289 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm uu____12289  in
                    (uu____12284, uu____12288)
                | uu____12292 ->
                    let uu____12303 =
                      let uu____12309 =
                        let uu____12311 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____12311
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____12309)
                       in
                    FStar_Errors.raise_error uu____12303
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____12331)::uu____12332 ->
                    let uu____12359 =
                      let uu____12364 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____12364
                       in
                    (match uu____12359 with
                     | (us_r,uu____12396) ->
                         let uu____12397 =
                           let uu____12402 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____12402
                            in
                         (match uu____12397 with
                          | (us_e,uu____12434) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____12437 =
                                  let uu____12438 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12438
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12437
                                  us_r
                                 in
                              let as_ens =
                                let uu____12440 =
                                  let uu____12441 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12441
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12440
                                  us_e
                                 in
                              let req =
                                let uu____12445 =
                                  let uu____12450 =
                                    let uu____12451 =
                                      let uu____12462 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12462]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12451
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____12450
                                   in
                                uu____12445 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____12502 =
                                  let uu____12507 =
                                    let uu____12508 =
                                      let uu____12519 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12519]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12508
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____12507
                                   in
                                uu____12502 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____12556 =
                                let uu____12559 = norm req  in
                                FStar_Pervasives_Native.Some uu____12559  in
                              let uu____12560 =
                                let uu____12561 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm uu____12561  in
                              (uu____12556, uu____12560)))
                | uu____12564 -> failwith "Impossible"))
  
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
        (let uu____12603 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____12603
         then
           let uu____12608 = FStar_Syntax_Print.term_to_string tm  in
           let uu____12610 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____12608
             uu____12610
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
      fun head  ->
        fun arg  ->
          let tm =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (head, [arg]))
              FStar_Pervasives_Native.None head.FStar_Syntax_Syntax.pos
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
          (let uu____12669 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____12669
           then
             let uu____12674 = FStar_Syntax_Print.term_to_string tm  in
             let uu____12676 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____12674
               uu____12676
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____12687 =
      let uu____12689 =
        let uu____12690 = FStar_Syntax_Subst.compress t  in
        uu____12690.FStar_Syntax_Syntax.n  in
      match uu____12689 with
      | FStar_Syntax_Syntax.Tm_app uu____12694 -> false
      | uu____12712 -> true  in
    if uu____12687
    then t
    else
      (let uu____12717 = FStar_Syntax_Util.head_and_args t  in
       match uu____12717 with
       | (head,args) ->
           let uu____12760 =
             let uu____12762 =
               let uu____12763 = FStar_Syntax_Subst.compress head  in
               uu____12763.FStar_Syntax_Syntax.n  in
             match uu____12762 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____12768 -> false  in
           if uu____12760
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____12800 ->
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
          ((let uu____12847 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____12847
            then
              let uu____12850 = FStar_Syntax_Print.term_to_string e  in
              let uu____12852 = FStar_Syntax_Print.term_to_string t  in
              let uu____12854 =
                let uu____12856 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____12856
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____12850 uu____12852 uu____12854
            else ());
           (let unfolded_arrow_formals t1 =
              let rec aux bs t2 =
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf env t2  in
                let uu____12892 = FStar_Syntax_Util.arrow_formals t3  in
                match uu____12892 with
                | (bs',t4) ->
                    (match bs' with
                     | [] -> bs
                     | bs'1 -> aux (FStar_List.append bs bs'1) t4)
                 in
              aux [] t1  in
            let number_of_implicits t1 =
              let formals = unfolded_arrow_formals t1  in
              let n_implicits =
                let uu____12926 =
                  FStar_All.pipe_right formals
                    (FStar_Util.prefix_until
                       (fun uu____13004  ->
                          match uu____13004 with
                          | (uu____13012,imp) ->
                              (FStar_Option.isNone imp) ||
                                (let uu____13019 =
                                   FStar_Syntax_Util.eq_aqual imp
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Equality)
                                    in
                                 uu____13019 = FStar_Syntax_Util.Equal)))
                   in
                match uu____12926 with
                | FStar_Pervasives_Native.None  -> FStar_List.length formals
                | FStar_Pervasives_Native.Some
                    (implicits,_first_explicit,_rest) ->
                    FStar_List.length implicits
                 in
              n_implicits  in
            let inst_n_binders t1 =
              let uu____13138 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____13138 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____13152 =
                      let uu____13158 =
                        let uu____13160 = FStar_Util.string_of_int n_expected
                           in
                        let uu____13162 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____13164 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____13160 uu____13162 uu____13164
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____13158)
                       in
                    let uu____13168 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____13152 uu____13168
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_13186 =
              match uu___7_13186 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____13229 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____13229 with
                 | (bs1,c1) ->
                     let rec aux subst inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some
                          uu____13360,uu____13347) when
                           uu____13360 = Prims.int_zero ->
                           ([], bs2, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____13393,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____13395))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____13429 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____13429 with
                            | (v,uu____13470,g) ->
                                ((let uu____13485 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13485
                                  then
                                    let uu____13488 =
                                      FStar_Syntax_Print.term_to_string v  in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____13488
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst
                                     in
                                  let uu____13498 =
                                    aux subst1 (decr_inst inst_n) rest  in
                                  match uu____13498 with
                                  | (args,bs3,subst2,g') ->
                                      let uu____13591 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____13591))))
                       | (uu____13618,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____13655 =
                             let uu____13668 =
                               let uu____13675 =
                                 let uu____13680 = FStar_Dyn.mkdyn env  in
                                 (uu____13680, tau)  in
                               FStar_Pervasives_Native.Some uu____13675  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____13668
                              in
                           (match uu____13655 with
                            | (v,uu____13713,g) ->
                                ((let uu____13728 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13728
                                  then
                                    let uu____13731 =
                                      FStar_Syntax_Print.term_to_string v  in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____13731
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst
                                     in
                                  let uu____13741 =
                                    aux subst1 (decr_inst inst_n) rest  in
                                  match uu____13741 with
                                  | (args,bs3,subst2,g') ->
                                      let uu____13834 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____13834))))
                       | (uu____13861,bs3) ->
                           ([], bs3, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____13909 =
                       let uu____13936 = inst_n_binders t1  in
                       aux [] uu____13936 bs1  in
                     (match uu____13909 with
                      | (args,bs2,subst,guard) ->
                          (match (args, bs2) with
                           | ([],uu____14008) -> (e, torig, guard)
                           | (uu____14039,[]) when
                               let uu____14070 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____14070 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____14072 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____14100 ->
                                     FStar_Syntax_Util.arrow bs2 c1
                                  in
                               let t3 = FStar_Syntax_Subst.subst subst t2  in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   FStar_Pervasives_Native.None
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               (e1, t3, guard))))
            | uu____14113 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs  ->
    let uu____14125 =
      let uu____14129 = FStar_Util.set_elements univs  in
      FStar_All.pipe_right uu____14129
        (FStar_List.map
           (fun u  ->
              let uu____14141 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____14141 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____14125 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____14169 = FStar_Util.set_is_empty x  in
      if uu____14169
      then []
      else
        (let s =
           let uu____14189 =
             let uu____14192 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____14192  in
           FStar_All.pipe_right uu____14189 FStar_Util.set_elements  in
         (let uu____14210 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____14210
          then
            let uu____14215 =
              let uu____14217 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____14217  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____14215
          else ());
         (let r =
            let uu____14226 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____14226  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____14271 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____14271
                     then
                       let uu____14276 =
                         let uu____14278 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____14278
                          in
                       let uu____14282 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____14284 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____14276 uu____14282 uu____14284
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
      let univnames =
        let uu____14314 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____14314 FStar_Util.set_elements  in
      univnames
  
let (check_universe_generalization :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun explicit_univ_names  ->
    fun generalized_univ_names  ->
      fun t  ->
        match (explicit_univ_names, generalized_univ_names) with
        | ([],uu____14353) -> generalized_univ_names
        | (uu____14360,[]) -> explicit_univ_names
        | uu____14367 ->
            let uu____14376 =
              let uu____14382 =
                let uu____14384 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____14384
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____14382)
               in
            FStar_Errors.raise_error uu____14376 t.FStar_Syntax_Syntax.pos
  
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
      let univnames = gather_free_univnames env t  in
      (let uu____14406 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____14406
       then
         let uu____14411 = FStar_Syntax_Print.term_to_string t  in
         let uu____14413 = FStar_Syntax_Print.univ_names_to_string univnames
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____14411 uu____14413
       else ());
      (let univs = FStar_Syntax_Free.univs t  in
       (let uu____14422 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____14422
        then
          let uu____14427 = string_of_univs univs  in
          FStar_Util.print1 "univs to gen : %s\n" uu____14427
        else ());
       (let gen = gen_univs env univs  in
        (let uu____14436 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____14436
         then
           let uu____14441 = FStar_Syntax_Print.term_to_string t  in
           let uu____14443 = FStar_Syntax_Print.univ_names_to_string gen  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____14441 uu____14443
         else ());
        (let univs1 = check_universe_generalization univnames gen t0  in
         let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t  in
         let ts = FStar_Syntax_Subst.close_univ_vars univs1 t1  in
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
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        let uu____14527 =
          let uu____14529 =
            FStar_Util.for_all
              (fun uu____14543  ->
                 match uu____14543 with
                 | (uu____14553,uu____14554,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____14529  in
        if uu____14527
        then FStar_Pervasives_Native.None
        else
          (let norm c =
             (let uu____14606 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____14606
              then
                let uu____14609 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____14609
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____14616 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____14616
               then
                 let uu____14619 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____14619
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____14637 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____14637 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____14671 =
             match uu____14671 with
             | (lbname,e,c) ->
                 let c1 = norm c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____14708 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____14708
                   then
                     let uu____14713 =
                       let uu____14715 =
                         let uu____14719 = FStar_Util.set_elements univs  in
                         FStar_All.pipe_right uu____14719
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____14715
                         (FStar_String.concat ", ")
                        in
                     let uu____14775 =
                       let uu____14777 =
                         let uu____14781 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____14781
                           (FStar_List.map
                              (fun u  ->
                                 let uu____14794 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____14796 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____14794
                                   uu____14796))
                          in
                       FStar_All.pipe_right uu____14777
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____14713
                       uu____14775
                   else ());
                  (let univs1 =
                     let uu____14810 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs1  ->
                          fun uv  ->
                            let uu____14822 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs1 uu____14822) univs
                       uu____14810
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____14829 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____14829
                    then
                      let uu____14834 =
                        let uu____14836 =
                          let uu____14840 = FStar_Util.set_elements univs1
                             in
                          FStar_All.pipe_right uu____14840
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____14836
                          (FStar_String.concat ", ")
                         in
                      let uu____14896 =
                        let uu____14898 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____14912 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____14914 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____14912
                                    uu____14914))
                           in
                        FStar_All.pipe_right uu____14898
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____14834 uu____14896
                    else ());
                   (univs1, uvs, (lbname, e, c1))))
              in
           let uu____14935 =
             let uu____14952 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____14952  in
           match uu____14935 with
           | (univs,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____15042 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____15042
                 then ()
                 else
                   (let uu____15047 = lec_hd  in
                    match uu____15047 with
                    | (lb1,uu____15055,uu____15056) ->
                        let uu____15057 = lec2  in
                        (match uu____15057 with
                         | (lb2,uu____15065,uu____15066) ->
                             let msg =
                               let uu____15069 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15071 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____15069 uu____15071
                                in
                             let uu____15074 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____15074))
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
                 let uu____15142 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____15142
                 then ()
                 else
                   (let uu____15147 = lec_hd  in
                    match uu____15147 with
                    | (lb1,uu____15155,uu____15156) ->
                        let uu____15157 = lec2  in
                        (match uu____15157 with
                         | (lb2,uu____15165,uu____15166) ->
                             let msg =
                               let uu____15169 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15171 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____15169 uu____15171
                                in
                             let uu____15174 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____15174))
                  in
               let lecs1 =
                 let uu____15185 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____15238 = univs_and_uvars_of_lec this_lec  in
                        match uu____15238 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____15185 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail rng k =
                   let uu____15348 = lec_hd  in
                   match uu____15348 with
                   | (lbname,e,c) ->
                       let uu____15358 =
                         let uu____15364 =
                           let uu____15366 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____15368 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____15370 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____15366 uu____15368 uu____15370
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____15364)
                          in
                       FStar_Errors.raise_error uu____15358 rng
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____15392 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____15392 with
                         | FStar_Pervasives_Native.Some uu____15401 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____15409 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____15413 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____15413 with
                              | (bs,kres) ->
                                  ((let uu____15433 =
                                      let uu____15434 =
                                        let uu____15437 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____15437
                                         in
                                      uu____15434.FStar_Syntax_Syntax.n  in
                                    match uu____15433 with
                                    | FStar_Syntax_Syntax.Tm_type uu____15438
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____15442 =
                                          let uu____15444 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____15444  in
                                        if uu____15442
                                        then
                                          fail
                                            u.FStar_Syntax_Syntax.ctx_uvar_range
                                            kres
                                        else ()
                                    | uu____15449 ->
                                        fail
                                          u.FStar_Syntax_Syntax.ctx_uvar_range
                                          kres);
                                   (let a =
                                      let uu____15451 =
                                        let uu____15454 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun uu____15457  ->
                                             FStar_Pervasives_Native.Some
                                               uu____15457) uu____15454
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____15451
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____15465 ->
                                          let uu____15466 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____15466
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
               let gen_univs1 = gen_univs env univs  in
               let gen_tvars = gen_types uvs  in
               let ecs =
                 FStar_All.pipe_right lecs2
                   (FStar_List.map
                      (fun uu____15569  ->
                         match uu____15569 with
                         | (lbname,e,c) ->
                             let uu____15615 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____15676 ->
                                   let uu____15689 = (e, c)  in
                                   (match uu____15689 with
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
                                                (fun uu____15729  ->
                                                   match uu____15729 with
                                                   | (x,uu____15735) ->
                                                       let uu____15736 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____15736)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____15754 =
                                                let uu____15756 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____15756
                                                 in
                                              if uu____15754
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
                                          let uu____15765 =
                                            let uu____15766 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____15766.FStar_Syntax_Syntax.n
                                             in
                                          match uu____15765 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____15791 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____15791 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____15802 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____15806 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____15806, gen_tvars))
                                in
                             (match uu____15615 with
                              | (e1,c1,gvs) ->
                                  (lbname, gen_univs1, e1, c1, gvs))))
                  in
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
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        (let uu____15953 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____15953
         then
           let uu____15956 =
             let uu____15958 =
               FStar_List.map
                 (fun uu____15973  ->
                    match uu____15973 with
                    | (lb,uu____15982,uu____15983) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____15958 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____15956
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____16009  ->
                match uu____16009 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____16038 = gen env is_rec lecs  in
           match uu____16038 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____16137  ->
                       match uu____16137 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____16199 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____16199
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____16247  ->
                           match uu____16247 with
                           | (l,us,e,c,gvs) ->
                               let uu____16281 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____16283 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____16285 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____16287 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____16289 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____16281 uu____16283 uu____16285
                                 uu____16287 uu____16289))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames  ->
              fun uu____16334  ->
                match uu____16334 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____16378 =
                      check_universe_generalization univnames
                        generalized_univs t
                       in
                    (l, uu____16378, t, c, gvs)) univnames_lecs
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
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        let uu____16433 =
          let uu____16437 =
            let uu____16439 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____16439  in
          FStar_Pervasives_Native.Some uu____16437  in
        FStar_Profiling.profile
          (fun uu____16456  -> generalize' env is_rec lecs) uu____16433
          "FStar.TypeChecker.Util.generalize"
  
let (check_has_type :
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
          let check env2 t1 t21 =
            if env2.FStar_TypeChecker_Env.use_eq_strict
            then
              let uu____16513 =
                FStar_TypeChecker_Rel.get_teq_predicate env2 t1 t21  in
              match uu____16513 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some f ->
                  let uu____16519 = FStar_TypeChecker_Env.apply_guard f e  in
                  FStar_All.pipe_right uu____16519
                    (fun uu____16522  ->
                       FStar_Pervasives_Native.Some uu____16522)
            else
              if env2.FStar_TypeChecker_Env.use_eq
              then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
              else
                (let uu____16531 =
                   FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                    in
                 match uu____16531 with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some f ->
                     let uu____16537 = FStar_TypeChecker_Env.apply_guard f e
                        in
                     FStar_All.pipe_left
                       (fun uu____16540  ->
                          FStar_Pervasives_Native.Some uu____16540)
                       uu____16537)
             in
          let uu____16541 = maybe_coerce_lc env1 e lc t2  in
          match uu____16541 with
          | (e1,lc1,g_c) ->
              let uu____16557 =
                check env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____16557 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16566 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____16572 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____16566 uu____16572
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____16581 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____16581
                     then
                       let uu____16586 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____16586
                     else ());
                    (let uu____16592 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (e1, lc1, uu____16592))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____16620 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____16620
         then
           let uu____16623 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____16623
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____16637 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____16637 with
         | (c,g_c) ->
             let uu____16649 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____16649
             then
               let uu____16657 =
                 let uu____16659 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____16659  in
               (uu____16657, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____16667 =
                    let uu____16668 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____16668
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____16667
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____16669 = check_trivial_precondition env c1  in
                match uu____16669 with
                | (ct,vc,g_pre) ->
                    ((let uu____16685 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____16685
                      then
                        let uu____16690 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____16690
                      else ());
                     (let uu____16695 =
                        let uu____16697 =
                          let uu____16698 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____16698  in
                        discharge uu____16697  in
                      let uu____16699 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____16695, uu____16699)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head  ->
    fun seen_args  ->
      let short_bin_op f uu___8_16733 =
        match uu___8_16733 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst,uu____16743)::[] -> f fst
        | uu____16768 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____16780 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____16780
          (fun uu____16781  ->
             FStar_TypeChecker_Common.NonTrivial uu____16781)
         in
      let op_or_e e =
        let uu____16792 =
          let uu____16793 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____16793  in
        FStar_All.pipe_right uu____16792
          (fun uu____16796  ->
             FStar_TypeChecker_Common.NonTrivial uu____16796)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun uu____16803  ->
             FStar_TypeChecker_Common.NonTrivial uu____16803)
         in
      let op_or_t t =
        let uu____16814 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____16814
          (fun uu____16817  ->
             FStar_TypeChecker_Common.NonTrivial uu____16817)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun uu____16824  ->
             FStar_TypeChecker_Common.NonTrivial uu____16824)
         in
      let short_op_ite uu___9_16830 =
        match uu___9_16830 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____16840)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____16867)::[] ->
            let uu____16908 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____16908
              (fun uu____16909  ->
                 FStar_TypeChecker_Common.NonTrivial uu____16909)
        | uu____16910 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____16922 =
          let uu____16930 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____16930)  in
        let uu____16938 =
          let uu____16948 =
            let uu____16956 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____16956)  in
          let uu____16964 =
            let uu____16974 =
              let uu____16982 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____16982)  in
            let uu____16990 =
              let uu____17000 =
                let uu____17008 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____17008)  in
              let uu____17016 =
                let uu____17026 =
                  let uu____17034 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____17034)  in
                [uu____17026; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____17000 :: uu____17016  in
            uu____16974 :: uu____16990  in
          uu____16948 :: uu____16964  in
        uu____16922 :: uu____16938  in
      match head.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____17096 =
            FStar_Util.find_map table
              (fun uu____17111  ->
                 match uu____17111 with
                 | (x,mk) ->
                     let uu____17128 = FStar_Ident.lid_equals x lid  in
                     if uu____17128
                     then
                       let uu____17133 = mk seen_args  in
                       FStar_Pervasives_Native.Some uu____17133
                     else FStar_Pervasives_Native.None)
             in
          (match uu____17096 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____17137 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____17145 =
      let uu____17146 = FStar_Syntax_Util.un_uinst l  in
      uu____17146.FStar_Syntax_Syntax.n  in
    match uu____17145 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____17151 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd,uu____17187)::uu____17188 -> FStar_Syntax_Syntax.range_of_bv hd
        | uu____17207 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____17216,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____17217))::uu____17218 -> bs
      | uu____17236 ->
          let uu____17237 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____17237 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____17241 =
                 let uu____17242 = FStar_Syntax_Subst.compress t  in
                 uu____17242.FStar_Syntax_Syntax.n  in
               (match uu____17241 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____17246) ->
                    let uu____17267 =
                      FStar_Util.prefix_until
                        (fun uu___10_17307  ->
                           match uu___10_17307 with
                           | (uu____17315,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____17316)) ->
                               false
                           | uu____17321 -> true) bs'
                       in
                    (match uu____17267 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____17357,uu____17358) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____17430,uu____17431) ->
                         let uu____17504 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____17525  ->
                                   match uu____17525 with
                                   | (x,uu____17534) ->
                                       let uu____17539 =
                                         FStar_Ident.text_of_id
                                           x.FStar_Syntax_Syntax.ppname
                                          in
                                       FStar_Util.starts_with uu____17539 "'"))
                            in
                         if uu____17504
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____17585  ->
                                     match uu____17585 with
                                     | (x,i) ->
                                         let uu____17604 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____17604, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____17615 -> bs))
  
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
            let uu____17644 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____17644
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
          let uu____17675 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____17675
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
        (let uu____17718 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____17718
         then
           ((let uu____17723 = FStar_Ident.string_of_lid lident  in
             d uu____17723);
            (let uu____17725 = FStar_Ident.string_of_lid lident  in
             let uu____17727 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____17725 uu____17727))
         else ());
        (let fv =
           let uu____17733 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____17733
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
         let uu____17745 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___2074_17747 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2074_17747.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2074_17747.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2074_17747.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2074_17747.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2074_17747.FStar_Syntax_Syntax.sigopts)
           }), uu____17745))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_17765 =
        match uu___11_17765 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____17768 -> false  in
      let reducibility uu___12_17776 =
        match uu___12_17776 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____17783 -> false  in
      let assumption uu___13_17791 =
        match uu___13_17791 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____17795 -> false  in
      let reification uu___14_17803 =
        match uu___14_17803 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____17806 -> true
        | uu____17808 -> false  in
      let inferred uu___15_17816 =
        match uu___15_17816 with
        | FStar_Syntax_Syntax.Discriminator uu____17818 -> true
        | FStar_Syntax_Syntax.Projector uu____17820 -> true
        | FStar_Syntax_Syntax.RecordType uu____17826 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____17836 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____17849 -> false  in
      let has_eq uu___16_17857 =
        match uu___16_17857 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____17861 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____17940 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____17947 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____17980 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____17980))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____18011 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____18011
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
           | FStar_Syntax_Syntax.Sig_bundle uu____18031 ->
               let uu____18040 =
                 let uu____18042 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_18048  ->
                           match uu___17_18048 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____18051 -> false))
                    in
                 Prims.op_Negation uu____18042  in
               if uu____18040
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____18058 -> ()
           | FStar_Syntax_Syntax.Sig_fail uu____18065 -> ()
           | uu____18078 ->
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
      let uu____18092 =
        let uu____18094 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_18100  ->
                  match uu___18_18100 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____18103 -> false))
           in
        FStar_All.pipe_right uu____18094 Prims.op_Negation  in
      if uu____18092
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____18124 =
            let uu____18130 =
              let uu____18132 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____18132 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____18130)  in
          FStar_Errors.raise_error uu____18124 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____18150 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____18158 =
            let uu____18160 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____18160  in
          if uu____18158 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____18171),uu____18172) ->
              ((let uu____18184 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____18184
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____18193 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____18193
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____18204 ->
              ((let uu____18214 =
                  let uu____18216 =
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
                  Prims.op_Negation uu____18216  in
                if uu____18214 then err'1 () else ());
               (let uu____18226 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_18232  ->
                           match uu___19_18232 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____18235 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____18226
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____18241 ->
              let uu____18248 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____18248 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____18256 ->
              let uu____18263 =
                let uu____18265 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____18265  in
              if uu____18263 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____18275 ->
              let uu____18276 =
                let uu____18278 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____18278  in
              if uu____18276 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18288 ->
              let uu____18301 =
                let uu____18303 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____18303  in
              if uu____18301 then err'1 () else ()
          | uu____18313 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____18352 =
          let uu____18353 = FStar_Syntax_Subst.compress t1  in
          uu____18353.FStar_Syntax_Syntax.n  in
        match uu____18352 with
        | FStar_Syntax_Syntax.Tm_arrow uu____18357 ->
            let uu____18372 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____18372 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____18381;
               FStar_Syntax_Syntax.index = uu____18382;
               FStar_Syntax_Syntax.sort = t2;_},uu____18384)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head,uu____18393) -> descend env head
        | FStar_Syntax_Syntax.Tm_uinst (head,uu____18419) -> descend env head
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____18425 -> false
      
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
        (let uu____18435 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____18435
         then
           let uu____18440 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____18440
         else ());
        res
       in aux g t
  
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
  fun env  ->
    fun r  ->
      fun eff_name  ->
        fun signature_ts  ->
          fun repr_ts_opt  ->
            fun u  ->
              fun a_tm  ->
                let fail t =
                  let uu____18505 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____18505 r  in
                let uu____18515 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____18515 with
                | (uu____18524,signature) ->
                    let uu____18526 =
                      let uu____18527 = FStar_Syntax_Subst.compress signature
                         in
                      uu____18527.FStar_Syntax_Syntax.n  in
                    (match uu____18526 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18535) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____18583 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____18599 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____18601 =
                                       FStar_Ident.string_of_lid eff_name  in
                                     let uu____18603 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____18599 uu____18601 uu____18603) r
                                 in
                              (match uu____18583 with
                               | (is,g) ->
                                   let uu____18616 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____18618 =
                                             let uu____18619 =
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 is
                                                in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = [u];
                                               FStar_Syntax_Syntax.effect_name
                                                 = eff_name;
                                               FStar_Syntax_Syntax.result_typ
                                                 = a_tm;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____18619;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____18618
                                            in
                                         let uu____18638 =
                                           let uu____18645 =
                                             let uu____18646 =
                                               let uu____18661 =
                                                 let uu____18670 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_unit
                                                    in
                                                 [uu____18670]  in
                                               (uu____18661, eff_c)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____18646
                                              in
                                           FStar_Syntax_Syntax.mk uu____18645
                                            in
                                         uu____18638
                                           FStar_Pervasives_Native.None r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____18701 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____18701
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____18710 =
                                           let uu____18715 =
                                             FStar_List.map
                                               FStar_Syntax_Syntax.as_arg
                                               (a_tm :: is)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____18715
                                            in
                                         uu____18710
                                           FStar_Pervasives_Native.None r
                                      in
                                   (uu____18616, g))
                          | uu____18724 -> fail signature)
                     | uu____18725 -> fail signature)
  
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
            let uu____18756 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____18756
              (fun ed  ->
                 let uu____18764 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____18764 u a_tm)
  
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
              let uu____18800 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____18800 with
              | (uu____18805,sig_tm) ->
                  let fail t =
                    let uu____18813 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____18813 r  in
                  let uu____18819 =
                    let uu____18820 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____18820.FStar_Syntax_Syntax.n  in
                  (match uu____18819 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18824) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____18847)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____18869 -> fail sig_tm)
                   | uu____18870 -> fail sig_tm)
  
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
          (let uu____18901 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsApp")
              in
           if uu____18901
           then
             let uu____18906 = FStar_Syntax_Print.comp_to_string c  in
             let uu____18908 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____18906 uu____18908
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____18915 =
             let uu____18928 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____18929 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____18928, (ct.FStar_Syntax_Syntax.result_typ), uu____18929)
              in
           match uu____18915 with
           | (u,a,c_is) ->
               let uu____18987 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____18987 with
                | (uu____18996,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____19007 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____19009 = FStar_Ident.string_of_lid tgt  in
                      let uu____19011 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____19007 uu____19009 s uu____19011
                       in
                    let uu____19014 =
                      let uu____19047 =
                        let uu____19048 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____19048.FStar_Syntax_Syntax.n  in
                      match uu____19047 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____19112 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____19112 with
                           | (a_b::bs1,c2) ->
                               let uu____19172 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               (a_b, uu____19172, c2))
                      | uu____19260 ->
                          let uu____19261 =
                            let uu____19267 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____19267)
                             in
                          FStar_Errors.raise_error uu____19261 r
                       in
                    (match uu____19014 with
                     | (a_b,(rest_bs,f_b::[]),lift_c) ->
                         let uu____19385 =
                           let uu____19392 =
                             let uu____19393 =
                               let uu____19394 =
                                 let uu____19401 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____19401, a)  in
                               FStar_Syntax_Syntax.NT uu____19394  in
                             [uu____19393]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____19392
                             (fun b  ->
                                let uu____19418 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____19420 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____19422 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____19424 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit for binder %s of %s~>%s at %s"
                                  uu____19418 uu____19420 uu____19422
                                  uu____19424) r
                            in
                         (match uu____19385 with
                          | (rest_bs_uvars,g) ->
                              let substs =
                                FStar_List.map2
                                  (fun b  ->
                                     fun t  ->
                                       let uu____19461 =
                                         let uu____19468 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____19468, t)  in
                                       FStar_Syntax_Syntax.NT uu____19461)
                                  (a_b :: rest_bs) (a :: rest_bs_uvars)
                                 in
                              let guard_f =
                                let f_sort =
                                  let uu____19487 =
                                    FStar_All.pipe_right
                                      (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                      (FStar_Syntax_Subst.subst substs)
                                     in
                                  FStar_All.pipe_right uu____19487
                                    FStar_Syntax_Subst.compress
                                   in
                                let f_sort_is =
                                  let uu____19493 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env ct.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Syntax_Util.effect_indices_from_repr
                                    f_sort uu____19493 r
                                    "f binder of lift is not a repr"
                                   in
                                FStar_List.fold_left2
                                  (fun g1  ->
                                     fun i1  ->
                                       fun i2  ->
                                         (let uu____19513 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsRel")
                                             in
                                          if uu____19513
                                          then
                                            let uu____19518 =
                                              FStar_Syntax_Print.term_to_string
                                                i1
                                               in
                                            let uu____19520 =
                                              FStar_Syntax_Print.term_to_string
                                                i2
                                               in
                                            FStar_Util.print2
                                              "Layered Effects teq %s = %s\n"
                                              uu____19518 uu____19520
                                          else ());
                                         (let uu____19525 =
                                            FStar_TypeChecker_Rel.teq env i1
                                              i2
                                             in
                                          FStar_TypeChecker_Env.conj_guard g1
                                            uu____19525))
                                  FStar_TypeChecker_Env.trivial_guard c_is
                                  f_sort_is
                                 in
                              let lift_ct =
                                let uu____19527 =
                                  FStar_All.pipe_right lift_c
                                    (FStar_Syntax_Subst.subst_comp substs)
                                   in
                                FStar_All.pipe_right uu____19527
                                  FStar_Syntax_Util.comp_to_comp_typ
                                 in
                              let is =
                                let uu____19531 =
                                  FStar_TypeChecker_Env.is_layered_effect env
                                    tgt
                                   in
                                FStar_Syntax_Util.effect_indices_from_repr
                                  lift_ct.FStar_Syntax_Syntax.result_typ
                                  uu____19531 r
                                  "return type of lift is not a repr"
                                 in
                              let fml =
                                let uu____19535 =
                                  let uu____19540 =
                                    FStar_List.hd
                                      lift_ct.FStar_Syntax_Syntax.comp_univs
                                     in
                                  let uu____19541 =
                                    let uu____19542 =
                                      FStar_List.hd
                                        lift_ct.FStar_Syntax_Syntax.effect_args
                                       in
                                    FStar_Pervasives_Native.fst uu____19542
                                     in
                                  (uu____19540, uu____19541)  in
                                match uu____19535 with
                                | (u1,wp) ->
                                    FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                      env u1
                                      lift_ct.FStar_Syntax_Syntax.result_typ
                                      wp FStar_Range.dummyRange
                                 in
                              let c1 =
                                let uu____19566 =
                                  let uu____19567 =
                                    FStar_All.pipe_right is
                                      (FStar_List.map
                                         FStar_Syntax_Syntax.as_arg)
                                     in
                                  {
                                    FStar_Syntax_Syntax.comp_univs =
                                      (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                    FStar_Syntax_Syntax.effect_name = tgt;
                                    FStar_Syntax_Syntax.result_typ = a;
                                    FStar_Syntax_Syntax.effect_args =
                                      uu____19567;
                                    FStar_Syntax_Syntax.flags = []
                                  }  in
                                FStar_Syntax_Syntax.mk_Comp uu____19566  in
                              ((let uu____19591 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffectsApp")
                                   in
                                if uu____19591
                                then
                                  let uu____19596 =
                                    FStar_Syntax_Print.comp_to_string c1  in
                                  FStar_Util.print1 "} Lifted comp: %s\n"
                                    uu____19596
                                else ());
                               (let uu____19601 =
                                  let uu____19602 =
                                    FStar_TypeChecker_Env.conj_guard g
                                      guard_f
                                     in
                                  let uu____19603 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         fml)
                                     in
                                  FStar_TypeChecker_Env.conj_guard
                                    uu____19602 uu____19603
                                   in
                                (c1, uu____19601)))))))
  
let lift_tf_layered_effect_term :
  'uuuuuu19617 .
    'uuuuuu19617 ->
      FStar_Syntax_Syntax.sub_eff ->
        FStar_Syntax_Syntax.universe ->
          FStar_Syntax_Syntax.typ ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun sub  ->
      fun u  ->
        fun a  ->
          fun e  ->
            let lift =
              let uu____19646 =
                let uu____19651 =
                  FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____19651
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____19646 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____19694 =
                let uu____19695 =
                  let uu____19698 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____19698
                    FStar_Syntax_Subst.compress
                   in
                uu____19695.FStar_Syntax_Syntax.n  in
              match uu____19694 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____19721::bs,uu____19723)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____19763 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____19763
                    FStar_Pervasives_Native.fst
              | uu____19869 ->
                  let uu____19870 =
                    let uu____19876 =
                      let uu____19878 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____19878
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____19876)  in
                  FStar_Errors.raise_error uu____19870
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____19905 = FStar_Syntax_Syntax.as_arg a  in
              let uu____19914 =
                let uu____19925 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____19961  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____19968 =
                  let uu____19979 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____19979]  in
                FStar_List.append uu____19925 uu____19968  in
              uu____19905 :: uu____19914  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index  ->
        let uu____20050 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____20050 with
        | (uu____20055,t) ->
            let err n =
              let uu____20065 =
                let uu____20071 =
                  let uu____20073 = FStar_Ident.string_of_lid datacon  in
                  let uu____20075 = FStar_Util.string_of_int n  in
                  let uu____20077 = FStar_Util.string_of_int index  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____20073 uu____20075 uu____20077
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____20071)
                 in
              let uu____20081 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____20065 uu____20081  in
            let uu____20082 =
              let uu____20083 = FStar_Syntax_Subst.compress t  in
              uu____20083.FStar_Syntax_Syntax.n  in
            (match uu____20082 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____20087) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____20142  ->
                           match uu____20142 with
                           | (uu____20150,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____20159 -> true)))
                    in
                 if (FStar_List.length bs1) <= index
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index  in
                    FStar_Syntax_Util.mk_field_projector_name datacon
                      (FStar_Pervasives_Native.fst b) index)
             | uu____20193 -> err Prims.int_zero)
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub  ->
      let uu____20206 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub.FStar_Syntax_Syntax.target)
         in
      if uu____20206
      then
        let uu____20209 =
          let uu____20222 =
            FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub.FStar_Syntax_Syntax.target uu____20222
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____20209;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____20257 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____20257 with
           | (uu____20266,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____20285 =
                 let uu____20286 =
                   let uu___2446_20287 = ct  in
                   let uu____20288 =
                     let uu____20299 =
                       let uu____20308 =
                         let uu____20309 =
                           let uu____20316 =
                             let uu____20317 =
                               let uu____20334 =
                                 let uu____20345 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____20345; wp]  in
                               (lift_t, uu____20334)  in
                             FStar_Syntax_Syntax.Tm_app uu____20317  in
                           FStar_Syntax_Syntax.mk uu____20316  in
                         uu____20309 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____20308
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____20299]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2446_20287.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2446_20287.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____20288;
                     FStar_Syntax_Syntax.flags =
                       (uu___2446_20287.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____20286  in
               (uu____20285, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____20445 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____20445 with
           | (uu____20452,lift_t) ->
               let uu____20454 =
                 let uu____20461 =
                   let uu____20462 =
                     let uu____20479 =
                       let uu____20490 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____20499 =
                         let uu____20510 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____20519 =
                           let uu____20530 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____20530]  in
                         uu____20510 :: uu____20519  in
                       uu____20490 :: uu____20499  in
                     (lift_t, uu____20479)  in
                   FStar_Syntax_Syntax.Tm_app uu____20462  in
                 FStar_Syntax_Syntax.mk uu____20461  in
               uu____20454 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____20583 =
           let uu____20596 =
             FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____20596 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____20583;
           FStar_TypeChecker_Env.mlift_term =
             (match sub.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____20632  ->
                        fun uu____20633  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun sub  ->
      let uu____20656 = get_mlift_for_subeff env sub  in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub.FStar_Syntax_Syntax.source sub.FStar_Syntax_Syntax.target
        uu____20656
  
let (update_env_polymonadic_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.tscheme -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      fun n  ->
        fun p  ->
          fun ty  ->
            FStar_TypeChecker_Env.add_polymonadic_bind env m n p
              (fun env1  ->
                 fun c1  ->
                   fun bv_opt  ->
                     fun c2  ->
                       fun flags  ->
                         fun r  ->
                           mk_indexed_bind env1 m n p ty c1 bv_opt c2 flags r)
  