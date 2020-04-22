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
                   (FStar_Options.Other "LayeredEffects")
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
                                 "implicit var for binder %s of %s at %s"
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
                                   (FStar_Options.Other "LayeredEffects")
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
                      (FStar_Options.Other "LayeredEffects")
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
                              (FStar_Options.Other "LayeredEffects")
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
                           (FStar_Options.Other "LayeredEffects")
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
                             let uu____3615 =
                               FStar_List.hd
                                 ct1.FStar_Syntax_Syntax.comp_univs
                                in
                             let uu____3616 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 ct1.FStar_Syntax_Syntax.effect_args
                                in
                             (uu____3615,
                               (ct1.FStar_Syntax_Syntax.result_typ),
                               uu____3616)
                              in
                           (match uu____3604 with
                            | (u1,t1,is1) ->
                                let uu____3650 =
                                  let uu____3661 =
                                    FStar_List.hd
                                      ct2.FStar_Syntax_Syntax.comp_univs
                                     in
                                  let uu____3662 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst
                                      ct2.FStar_Syntax_Syntax.effect_args
                                     in
                                  (uu____3661,
                                    (ct2.FStar_Syntax_Syntax.result_typ),
                                    uu____3662)
                                   in
                                (match uu____3650 with
                                 | (u2,t2,is2) ->
                                     let uu____3696 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         bind_t [u1; u2]
                                        in
                                     (match uu____3696 with
                                      | (uu____3705,bind_t1) ->
                                          let bind_t_shape_error s =
                                            let uu____3720 =
                                              let uu____3722 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t1
                                                 in
                                              FStar_Util.format2
                                                "bind %s does not have proper shape (reason:%s)"
                                                uu____3722 s
                                               in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu____3720)
                                             in
                                          let uu____3726 =
                                            let uu____3771 =
                                              let uu____3772 =
                                                FStar_Syntax_Subst.compress
                                                  bind_t1
                                                 in
                                              uu____3772.FStar_Syntax_Syntax.n
                                               in
                                            match uu____3771 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs,c) when
                                                (FStar_List.length bs) >=
                                                  (Prims.of_int (4))
                                                ->
                                                let uu____3848 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs c
                                                   in
                                                (match uu____3848 with
                                                 | (a_b::b_b::bs1,c1) ->
                                                     let uu____3933 =
                                                       let uu____3960 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2)))
                                                           bs1
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____3960
                                                         (fun uu____4045  ->
                                                            match uu____4045
                                                            with
                                                            | (l1,l2) ->
                                                                let uu____4126
                                                                  =
                                                                  FStar_List.hd
                                                                    l2
                                                                   in
                                                                let uu____4139
                                                                  =
                                                                  let uu____4146
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                  FStar_List.hd
                                                                    uu____4146
                                                                   in
                                                                (l1,
                                                                  uu____4126,
                                                                  uu____4139))
                                                        in
                                                     (match uu____3933 with
                                                      | (rest_bs,f_b,g_b) ->
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b, c1)))
                                            | uu____4306 ->
                                                let uu____4307 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders"
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____4307 r1
                                             in
                                          (match uu____3726 with
                                           | (a_b,b_b,rest_bs,f_b,g_b,bind_c)
                                               ->
                                               let uu____4432 =
                                                 let uu____4439 =
                                                   let uu____4440 =
                                                     let uu____4441 =
                                                       let uu____4448 =
                                                         FStar_All.pipe_right
                                                           a_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       (uu____4448, t1)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____4441
                                                      in
                                                   let uu____4459 =
                                                     let uu____4462 =
                                                       let uu____4463 =
                                                         let uu____4470 =
                                                           FStar_All.pipe_right
                                                             b_b
                                                             FStar_Pervasives_Native.fst
                                                            in
                                                         (uu____4470, t2)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____4463
                                                        in
                                                     [uu____4462]  in
                                                   uu____4440 :: uu____4459
                                                    in
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs uu____4439
                                                   (fun b1  ->
                                                      let uu____4486 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1
                                                         in
                                                      let uu____4488 =
                                                        let uu____4490 =
                                                          FStar_Ident.string_of_lid
                                                            m
                                                           in
                                                        let uu____4492 =
                                                          FStar_Ident.string_of_lid
                                                            n
                                                           in
                                                        let uu____4494 =
                                                          FStar_Ident.string_of_lid
                                                            p
                                                           in
                                                        FStar_Util.format3
                                                          "(%s, %s) |> %s"
                                                          uu____4490
                                                          uu____4492
                                                          uu____4494
                                                         in
                                                      let uu____4497 =
                                                        FStar_Range.string_of_range
                                                          r1
                                                         in
                                                      FStar_Util.format3
                                                        "implicit var for binder %s of %s at %s"
                                                        uu____4486 uu____4488
                                                        uu____4497) r1
                                                  in
                                               (match uu____4432 with
                                                | (rest_bs_uvars,g_uvars) ->
                                                    let subst =
                                                      FStar_List.map2
                                                        (fun b1  ->
                                                           fun t  ->
                                                             let uu____4534 =
                                                               let uu____4541
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   b1
                                                                   FStar_Pervasives_Native.fst
                                                                  in
                                                               (uu____4541,
                                                                 t)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____4534)
                                                        (a_b :: b_b ::
                                                        rest_bs) (t1 :: t2 ::
                                                        rest_bs_uvars)
                                                       in
                                                    let f_guard =
                                                      let f_sort_is =
                                                        let uu____4568 =
                                                          let uu____4571 =
                                                            let uu____4572 =
                                                              let uu____4573
                                                                =
                                                                FStar_All.pipe_right
                                                                  f_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4573.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4572
                                                             in
                                                          let uu____4582 =
                                                            FStar_Syntax_Util.is_layered
                                                              m_ed
                                                             in
                                                          let uu____4584 =
                                                            let uu____4586 =
                                                              let uu____4588
                                                                =
                                                                let uu____4589
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    f_b
                                                                    FStar_Pervasives_Native.fst
                                                                   in
                                                                uu____4589.FStar_Syntax_Syntax.sort
                                                                 in
                                                              FStar_Syntax_Print.term_to_string
                                                                uu____4588
                                                               in
                                                            FStar_Util.format1
                                                              "bind f binder sort is not a repr (%s)"
                                                              uu____4586
                                                             in
                                                          FStar_Syntax_Util.effect_indices_from_repr
                                                            uu____4571
                                                            uu____4582 r1
                                                            uu____4584
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____4568
                                                          (FStar_List.map
                                                             (FStar_Syntax_Subst.subst
                                                                subst))
                                                         in
                                                      FStar_List.fold_left2
                                                        (fun g  ->
                                                           fun i1  ->
                                                             fun f_i1  ->
                                                               let uu____4610
                                                                 =
                                                                 FStar_TypeChecker_Rel.teq
                                                                   env i1
                                                                   f_i1
                                                                  in
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g uu____4610)
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
                                                        let uu____4629 =
                                                          let uu____4630 =
                                                            let uu____4633 =
                                                              let uu____4634
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4634.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4633
                                                             in
                                                          uu____4630.FStar_Syntax_Syntax.n
                                                           in
                                                        match uu____4629 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____4667 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c
                                                               in
                                                            (match uu____4667
                                                             with
                                                             | (bs1,c1) ->
                                                                 let bs_subst
                                                                   =
                                                                   let uu____4677
                                                                    =
                                                                    let uu____4684
                                                                    =
                                                                    let uu____4685
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____4685
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____4706
                                                                    =
                                                                    let uu____4709
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4709
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____4684,
                                                                    uu____4706)
                                                                     in
                                                                   FStar_Syntax_Syntax.NT
                                                                    uu____4677
                                                                    in
                                                                 let c2 =
                                                                   FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1
                                                                    in
                                                                 let uu____4723
                                                                   =
                                                                   let uu____4726
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2)  in
                                                                   let uu____4727
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed  in
                                                                   let uu____4729
                                                                    =
                                                                    let uu____4731
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2)  in
                                                                    FStar_Util.format1
                                                                    "bind g binder comp type is not a repr (%s)"
                                                                    uu____4731
                                                                     in
                                                                   FStar_Syntax_Util.effect_indices_from_repr
                                                                    uu____4726
                                                                    uu____4727
                                                                    r1
                                                                    uu____4729
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____4723
                                                                   (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst)))
                                                        | uu____4738 ->
                                                            failwith
                                                              "imspossible: mk_indexed_bind"
                                                         in
                                                      let env_g =
                                                        FStar_TypeChecker_Env.push_binders
                                                          env [x_a]
                                                         in
                                                      let uu____4755 =
                                                        FStar_List.fold_left2
                                                          (fun g  ->
                                                             fun i1  ->
                                                               fun g_i1  ->
                                                                 let uu____4763
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq
                                                                    env_g i1
                                                                    g_i1
                                                                    in
                                                                 FStar_TypeChecker_Env.conj_guard
                                                                   g
                                                                   uu____4763)
                                                          FStar_TypeChecker_Env.trivial_guard
                                                          is2 g_sort_is
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4755
                                                        (FStar_TypeChecker_Env.close_guard
                                                           env [x_a])
                                                       in
                                                    let bind_ct =
                                                      let uu____4777 =
                                                        FStar_All.pipe_right
                                                          bind_c
                                                          (FStar_Syntax_Subst.subst_comp
                                                             subst)
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4777
                                                        FStar_Syntax_Util.comp_to_comp_typ
                                                       in
                                                    let fml =
                                                      let uu____4779 =
                                                        let uu____4784 =
                                                          FStar_List.hd
                                                            bind_ct.FStar_Syntax_Syntax.comp_univs
                                                           in
                                                        let uu____4785 =
                                                          let uu____4786 =
                                                            FStar_List.hd
                                                              bind_ct.FStar_Syntax_Syntax.effect_args
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____4786
                                                           in
                                                        (uu____4784,
                                                          uu____4785)
                                                         in
                                                      match uu____4779 with
                                                      | (u,wp) ->
                                                          FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                            env u
                                                            bind_ct.FStar_Syntax_Syntax.result_typ
                                                            wp
                                                            FStar_Range.dummyRange
                                                       in
                                                    let is =
                                                      let uu____4812 =
                                                        FStar_Syntax_Subst.compress
                                                          bind_ct.FStar_Syntax_Syntax.result_typ
                                                         in
                                                      let uu____4813 =
                                                        FStar_Syntax_Util.is_layered
                                                          p_ed
                                                         in
                                                      let uu____4815 =
                                                        let uu____4817 =
                                                          FStar_Syntax_Print.term_to_string
                                                            bind_ct.FStar_Syntax_Syntax.result_typ
                                                           in
                                                        FStar_Util.format1
                                                          "bind ct result type not a repr (%s)"
                                                          uu____4817
                                                         in
                                                      FStar_Syntax_Util.effect_indices_from_repr
                                                        uu____4812 uu____4813
                                                        r1 uu____4815
                                                       in
                                                    let c =
                                                      let uu____4821 =
                                                        let uu____4822 =
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
                                                            = uu____4822;
                                                          FStar_Syntax_Syntax.flags
                                                            = flags
                                                        }  in
                                                      FStar_Syntax_Syntax.mk_Comp
                                                        uu____4821
                                                       in
                                                    ((let uu____4842 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "LayeredEffects")
                                                         in
                                                      if uu____4842
                                                      then
                                                        let uu____4847 =
                                                          FStar_Syntax_Print.comp_to_string
                                                            c
                                                           in
                                                        FStar_Util.print1
                                                          "} c after bind: %s\n"
                                                          uu____4847
                                                      else ());
                                                     (let uu____4852 =
                                                        let uu____4853 =
                                                          let uu____4856 =
                                                            let uu____4859 =
                                                              let uu____4862
                                                                =
                                                                let uu____4865
                                                                  =
                                                                  FStar_TypeChecker_Env.guard_of_guard_formula
                                                                    (
                                                                    FStar_TypeChecker_Common.NonTrivial
                                                                    fml)
                                                                   in
                                                                [uu____4865]
                                                                 in
                                                              g_guard ::
                                                                uu____4862
                                                               in
                                                            f_guard ::
                                                              uu____4859
                                                             in
                                                          g_uvars ::
                                                            uu____4856
                                                           in
                                                        FStar_TypeChecker_Env.conj_guards
                                                          uu____4853
                                                         in
                                                      (c, uu____4852)))))))))
  
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
                let uu____4910 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____4936 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____4936 with
                  | (a,kwp) ->
                      let uu____4967 = destruct_wp_comp ct1  in
                      let uu____4974 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____4967, uu____4974)
                   in
                match uu____4910 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____5027 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____5027]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____5047 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____5047]
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
                      let uu____5094 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____5103 =
                        let uu____5114 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____5123 =
                          let uu____5134 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____5143 =
                            let uu____5154 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____5163 =
                              let uu____5174 =
                                let uu____5183 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____5183  in
                              [uu____5174]  in
                            uu____5154 :: uu____5163  in
                          uu____5134 :: uu____5143  in
                        uu____5114 :: uu____5123  in
                      uu____5094 :: uu____5103  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____5236 =
                        let uu____5241 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_t1; u_t2] env md bind_wp
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5241 wp_args  in
                      uu____5236 FStar_Pervasives_Native.None
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
              let uu____5289 =
                let uu____5294 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
                let uu____5295 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
                (uu____5294, uu____5295)  in
              match uu____5289 with
              | (ct1,ct2) ->
                  let uu____5302 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name
                     in
                  (match uu____5302 with
                   | FStar_Pervasives_Native.Some (p,f_bind) ->
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None  ->
                       let uu____5353 = lift_comps env c1 c2 b Lift_for_bind
                          in
                       (match uu____5353 with
                        | (m,c11,c21,g_lift) ->
                            let uu____5370 =
                              let uu____5375 =
                                FStar_Syntax_Util.comp_to_comp_typ c11  in
                              let uu____5376 =
                                FStar_Syntax_Util.comp_to_comp_typ c21  in
                              (uu____5375, uu____5376)  in
                            (match uu____5370 with
                             | (ct11,ct21) ->
                                 let uu____5383 =
                                   let uu____5388 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m
                                      in
                                   if uu____5388
                                   then
                                     let bind_t =
                                       let uu____5396 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env)
                                          in
                                       FStar_All.pipe_right uu____5396
                                         FStar_Syntax_Util.get_bind_vc_combinator
                                        in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu____5399 =
                                        mk_wp_bind env m ct11 b ct21 flags r1
                                         in
                                      (uu____5399,
                                        FStar_TypeChecker_Env.trivial_guard))
                                    in
                                 (match uu____5383 with
                                  | (c,g_bind) ->
                                      let uu____5406 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind
                                         in
                                      (c, uu____5406)))))
  
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
            let uu____5442 =
              let uu____5443 =
                let uu____5454 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____5454]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____5443;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____5442  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____5499 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_5505  ->
              match uu___1_5505 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5508 -> false))
       in
    if uu____5499
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_5520  ->
              match uu___2_5520 with
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
        let uu____5548 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5548
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____5559 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____5559  in
           let pure_assume_wp1 =
             let uu____5564 = FStar_TypeChecker_Env.get_range env  in
             let uu____5565 =
               let uu____5570 =
                 let uu____5571 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____5571]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____5570  in
             uu____5565 FStar_Pervasives_Native.None uu____5564  in
           let uu____5604 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____5604)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5632 =
          let uu____5633 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5633 with
          | (c,g_c) ->
              let uu____5644 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5644
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5658 = weaken_comp env c f1  in
                     (match uu____5658 with
                      | (c1,g_w) ->
                          let uu____5669 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____5669)))
           in
        let uu____5670 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5670 weaken
  
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
                 let uu____5727 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____5727  in
               let pure_assert_wp1 =
                 let uu____5732 =
                   let uu____5737 =
                     let uu____5738 =
                       let uu____5747 = label_opt env reason r f  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                         uu____5747
                        in
                     [uu____5738]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____5737
                    in
                 uu____5732 FStar_Pervasives_Native.None r  in
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
            let uu____5817 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____5817
            then (lc, g0)
            else
              (let flags =
                 let uu____5829 =
                   let uu____5837 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____5837
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5829 with
                 | (maybe_trivial_post,flags) ->
                     let uu____5867 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_5875  ->
                               match uu___3_5875 with
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
                               | uu____5878 -> []))
                        in
                     FStar_List.append flags uu____5867
                  in
               let strengthen uu____5888 =
                 let uu____5889 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____5889 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____5908 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____5908 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____5915 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____5915
                              then
                                let uu____5919 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____5921 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____5919 uu____5921
                              else ());
                             (let uu____5926 =
                                strengthen_comp env reason c f flags  in
                              match uu____5926 with
                              | (c1,g_s) ->
                                  let uu____5937 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____5937))))
                  in
               let uu____5938 =
                 let uu____5939 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____5939
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____5938,
                 (let uu___689_5941 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___689_5941.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___689_5941.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___689_5941.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_5950  ->
            match uu___4_5950 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____5954 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____5983 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____5983
          then e
          else
            (let uu____5990 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____5993 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____5993)
                in
             if uu____5990
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
                | uu____6063 -> false  in
              if is_unit
              then
                let uu____6070 =
                  let uu____6072 =
                    let uu____6073 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____6073
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____6072
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____6070
                 then
                   let uu____6082 = FStar_Syntax_Subst.open_term_bv b phi  in
                   match uu____6082 with
                   | (b1,phi1) ->
                       let phi2 =
                         FStar_Syntax_Subst.subst
                           [FStar_Syntax_Syntax.NT
                              (b1, FStar_Syntax_Syntax.unit_const)] phi1
                          in
                       weaken_comp env c phi2
                 else
                   (let uu____6098 = close_wp_comp env [x] c  in
                    (uu____6098, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____6101 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
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
          fun uu____6129  ->
            match uu____6129 with
            | (b,lc2) ->
                let debug f =
                  let uu____6149 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____6149 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____6162 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____6162
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____6172 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____6172
                       then
                         let uu____6177 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____6177
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____6184 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____6184
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____6193 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____6193
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____6200 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____6200
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____6216 =
                  let uu____6217 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____6217
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____6225 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____6225, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____6228 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____6228 with
                     | (c1,g_c1) ->
                         let uu____6239 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____6239 with
                          | (c2,g_c2) ->
                              let trivial_guard =
                                let uu____6251 =
                                  match b with
                                  | FStar_Pervasives_Native.Some x ->
                                      let b1 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      let uu____6254 =
                                        FStar_Syntax_Syntax.is_null_binder b1
                                         in
                                      if uu____6254
                                      then g_c2
                                      else
                                        FStar_TypeChecker_Env.close_guard env
                                          [b1] g_c2
                                  | FStar_Pervasives_Native.None  -> g_c2  in
                                FStar_TypeChecker_Env.conj_guard g_c1
                                  uu____6251
                                 in
                              (debug
                                 (fun uu____6280  ->
                                    let uu____6281 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____6283 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____6288 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____6281 uu____6283 uu____6288);
                               (let aux uu____6306 =
                                  let uu____6307 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____6307
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____6338
                                        ->
                                        let uu____6339 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____6339
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____6371 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____6371
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____6418 =
                                  let aux_with_trivial_guard uu____6448 =
                                    let uu____6449 = aux ()  in
                                    match uu____6449 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c, trivial_guard, reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____6507 =
                                    let uu____6509 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____6509  in
                                  if uu____6507
                                  then
                                    let uu____6525 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____6525
                                     then
                                       FStar_Util.Inl
                                         (c2, trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____6552 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____6552))
                                  else
                                    (let uu____6569 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____6569
                                     then
                                       let close_with_type_of_x x c =
                                         let x1 =
                                           let uu___792_6600 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___792_6600.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___792_6600.FStar_Syntax_Syntax.index);
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
                                           let uu____6631 =
                                             let uu____6636 =
                                               FStar_All.pipe_right c2
                                                 (FStar_Syntax_Subst.subst_comp
                                                    [FStar_Syntax_Syntax.NT
                                                       (x, e)])
                                                in
                                             FStar_All.pipe_right uu____6636
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6631 with
                                            | (c21,g_close) ->
                                                let uu____6657 =
                                                  let uu____6665 =
                                                    let uu____6666 =
                                                      let uu____6669 =
                                                        let uu____6672 =
                                                          FStar_TypeChecker_Env.map_guard
                                                            g_c2
                                                            (FStar_Syntax_Subst.subst
                                                               [FStar_Syntax_Syntax.NT
                                                                  (x, e)])
                                                           in
                                                        [uu____6672; g_close]
                                                         in
                                                      g_c1 :: uu____6669  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6666
                                                     in
                                                  (c21, uu____6665, "c1 Tot")
                                                   in
                                                FStar_Util.Inl uu____6657)
                                       | (uu____6685,FStar_Pervasives_Native.Some
                                          x) ->
                                           let uu____6697 =
                                             FStar_All.pipe_right c2
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6697 with
                                            | (c21,g_close) ->
                                                let uu____6720 =
                                                  let uu____6728 =
                                                    let uu____6729 =
                                                      let uu____6732 =
                                                        let uu____6735 =
                                                          let uu____6736 =
                                                            let uu____6737 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____6737]  in
                                                          FStar_TypeChecker_Env.close_guard
                                                            env uu____6736
                                                            g_c2
                                                           in
                                                        [uu____6735; g_close]
                                                         in
                                                      g_c1 :: uu____6732  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6729
                                                     in
                                                  (c21, uu____6728,
                                                    "c1 Tot only close")
                                                   in
                                                FStar_Util.Inl uu____6720)
                                       | (uu____6766,uu____6767) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____6782 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____6782
                                        then
                                          let uu____6797 =
                                            let uu____6805 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____6805, trivial_guard,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____6797
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____6818 = try_simplify ()  in
                                match uu____6818 with
                                | FStar_Util.Inl (c,g,reason) ->
                                    (debug
                                       (fun uu____6853  ->
                                          let uu____6854 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____6854);
                                     (c, g))
                                | FStar_Util.Inr reason ->
                                    (debug
                                       (fun uu____6870  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 g =
                                        let uu____6901 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____6901 with
                                        | (c,g_bind) ->
                                            let uu____6912 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g g_bind
                                               in
                                            (c, uu____6912)
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
                                        let uu____6939 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____6939 with
                                        | (m,uu____6951,lift2) ->
                                            let uu____6953 =
                                              lift_comp env c22 lift2  in
                                            (match uu____6953 with
                                             | (c23,g2) ->
                                                 let uu____6964 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____6964 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let trivial =
                                                        let uu____6980 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____6980
                                                          FStar_Util.must
                                                         in
                                                      let vc1 =
                                                        let uu____6990 =
                                                          let uu____6995 =
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              trivial
                                                             in
                                                          let uu____6996 =
                                                            let uu____6997 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____7006 =
                                                              let uu____7017
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____7017]
                                                               in
                                                            uu____6997 ::
                                                              uu____7006
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____6995
                                                            uu____6996
                                                           in
                                                        uu____6990
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____7050 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____7050 with
                                                       | (c,g_s) ->
                                                           let uu____7065 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____7065))))
                                         in
                                      let uu____7066 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____7082 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____7082, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____7066 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____7098 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____7098
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____7107 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____7107
                                             then
                                               (debug
                                                  (fun uu____7121  ->
                                                     let uu____7122 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____7124 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____7122 uu____7124);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 let g =
                                                   let uu____7131 =
                                                     FStar_TypeChecker_Env.map_guard
                                                       g_c2
                                                       (FStar_Syntax_Subst.subst
                                                          [FStar_Syntax_Syntax.NT
                                                             (x, e1)])
                                                      in
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 uu____7131
                                                    in
                                                 mk_bind1 c1 b c21 g))
                                             else
                                               (let uu____7136 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____7139 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____7139)
                                                   in
                                                if uu____7136
                                                then
                                                  let e1' =
                                                    let uu____7164 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____7164
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug
                                                     (fun uu____7176  ->
                                                        let uu____7177 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____7179 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____7177
                                                          uu____7179);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug
                                                     (fun uu____7194  ->
                                                        let uu____7195 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____7197 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____7195
                                                          uu____7197);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____7204 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____7204
                                                       in
                                                    let uu____7205 =
                                                      let uu____7210 =
                                                        let uu____7211 =
                                                          let uu____7212 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____7212]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____7211
                                                         in
                                                      weaken_comp uu____7210
                                                        c21 x_eq_e
                                                       in
                                                    match uu____7205 with
                                                    | (c22,g_w) ->
                                                        let g =
                                                          let uu____7238 =
                                                            let uu____7239 =
                                                              let uu____7240
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x
                                                                 in
                                                              [uu____7240]
                                                               in
                                                            let uu____7259 =
                                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                                g_c2 x_eq_e
                                                               in
                                                            FStar_TypeChecker_Env.close_guard
                                                              env uu____7239
                                                              uu____7259
                                                             in
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g_c1 uu____7238
                                                           in
                                                        let uu____7260 =
                                                          mk_bind1 c1 b c22 g
                                                           in
                                                        (match uu____7260
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____7271 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____7271))))))
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
      | uu____7288 -> g2
  
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
            (let uu____7312 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____7312)
           in
        let flags =
          if should_return1
          then
            let uu____7320 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____7320
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine uu____7338 =
          let uu____7339 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____7339 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____7352 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____7352
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____7360 =
                  let uu____7362 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____7362  in
                (if uu____7360
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___917_7371 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___917_7371.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___917_7371.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___917_7371.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____7372 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____7372, g_c)
                 else
                   (let uu____7375 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____7375, g_c)))
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
                   let uu____7386 =
                     let uu____7387 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____7387
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____7386
                    in
                 let eq = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret
                     (FStar_TypeChecker_Common.NonTrivial eq)
                    in
                 let uu____7390 =
                   let uu____7395 =
                     let uu____7396 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____7396
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____7395  in
                 match uu____7390 with
                 | (bind_c,g_bind) ->
                     let uu____7405 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____7406 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____7405, uu____7406))
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
            fun uu____7442  ->
              match uu____7442 with
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
                    let uu____7454 =
                      ((let uu____7458 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____7458) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____7454
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____7476 =
        let uu____7477 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____7477  in
      FStar_Syntax_Syntax.fvar uu____7476 FStar_Syntax_Syntax.delta_constant
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
                  let uu____7527 =
                    let uu____7532 =
                      let uu____7533 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____7533 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7532 [u_a]
                     in
                  match uu____7527 with
                  | (uu____7544,conjunction) ->
                      let uu____7546 =
                        let uu____7555 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____7570 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____7555, uu____7570)  in
                      (match uu____7546 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____7616 =
                               let uu____7618 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____7618 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7616)
                              in
                           let uu____7622 =
                             let uu____7667 =
                               let uu____7668 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____7668.FStar_Syntax_Syntax.n  in
                             match uu____7667 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____7717) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____7749 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____7749 with
                                  | (a_b::bs1,body1) ->
                                      let uu____7821 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____7821 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____7969 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____7969)))
                             | uu____8002 ->
                                 let uu____8003 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____8003 r
                              in
                           (match uu____7622 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____8128 =
                                  let uu____8135 =
                                    let uu____8136 =
                                      let uu____8137 =
                                        let uu____8144 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____8144, a)  in
                                      FStar_Syntax_Syntax.NT uu____8137  in
                                    [uu____8136]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____8135
                                    (fun b  ->
                                       let uu____8160 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____8162 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____8164 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____8160 uu____8162 uu____8164) r
                                   in
                                (match uu____8128 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____8202 =
                                                let uu____8209 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____8209, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____8202) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____8248 =
                                           let uu____8249 =
                                             let uu____8252 =
                                               let uu____8253 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8253.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8252
                                              in
                                           uu____8249.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8248 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8264,uu____8265::is) ->
                                             let uu____8307 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8307
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8340 ->
                                             let uu____8341 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8341 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____8357 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8357)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____8362 =
                                           let uu____8363 =
                                             let uu____8366 =
                                               let uu____8367 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8367.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8366
                                              in
                                           uu____8363.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8362 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8378,uu____8379::is) ->
                                             let uu____8421 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8421
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8454 ->
                                             let uu____8455 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8455 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____8471 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8471)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____8476 =
                                         let uu____8477 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____8477.FStar_Syntax_Syntax.n  in
                                       match uu____8476 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8482,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8537 ->
                                           let uu____8538 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____8538 r
                                        in
                                     let uu____8547 =
                                       let uu____8548 =
                                         let uu____8549 =
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
                                             uu____8549;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____8548
                                        in
                                     let uu____8572 =
                                       let uu____8573 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8573 g_guard
                                        in
                                     (uu____8547, uu____8572))))
  
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
                fun uu____8618  ->
                  let if_then_else =
                    let uu____8624 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____8624 FStar_Util.must  in
                  let uu____8631 = destruct_wp_comp ct1  in
                  match uu____8631 with
                  | (uu____8642,uu____8643,wp_t) ->
                      let uu____8645 = destruct_wp_comp ct2  in
                      (match uu____8645 with
                       | (uu____8656,uu____8657,wp_e) ->
                           let wp =
                             let uu____8662 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             let uu____8663 =
                               let uu____8668 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_a] env ed if_then_else
                                  in
                               let uu____8669 =
                                 let uu____8670 =
                                   FStar_Syntax_Syntax.as_arg a  in
                                 let uu____8679 =
                                   let uu____8690 =
                                     FStar_Syntax_Syntax.as_arg p  in
                                   let uu____8699 =
                                     let uu____8710 =
                                       FStar_Syntax_Syntax.as_arg wp_t  in
                                     let uu____8719 =
                                       let uu____8730 =
                                         FStar_Syntax_Syntax.as_arg wp_e  in
                                       [uu____8730]  in
                                     uu____8710 :: uu____8719  in
                                   uu____8690 :: uu____8699  in
                                 uu____8670 :: uu____8679  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____8668
                                 uu____8669
                                in
                             uu____8663 FStar_Pervasives_Native.None
                               uu____8662
                              in
                           let uu____8779 = mk_comp ed u_a a wp []  in
                           (uu____8779, FStar_TypeChecker_Env.trivial_guard))
  
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
            let uu____8833 =
              let uu____8834 =
                FStar_All.pipe_right scrutinee FStar_Syntax_Syntax.mk_binder
                 in
              [uu____8834]  in
            FStar_TypeChecker_Env.push_binders env0 uu____8833  in
          let eff =
            FStar_List.fold_left
              (fun eff  ->
                 fun uu____8881  ->
                   match uu____8881 with
                   | (uu____8895,eff_label,uu____8897,uu____8898) ->
                       join_effects env eff eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases
             in
          let uu____8911 =
            let uu____8919 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu____8957  ->
                      match uu____8957 with
                      | (uu____8972,uu____8973,flags,uu____8975) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___5_8992  ->
                                  match uu___5_8992 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                      true
                                  | uu____8995 -> false))))
               in
            if uu____8919
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, [])  in
          match uu____8911 with
          | (should_not_inline_whole_match,bind_cases_flags) ->
              let bind_cases uu____9032 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                   in
                let uu____9034 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                   in
                if uu____9034
                then
                  let uu____9041 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                     in
                  (uu____9041, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let default_case =
                     let post_k =
                       let uu____9048 =
                         let uu____9057 =
                           FStar_Syntax_Syntax.null_binder res_t  in
                         [uu____9057]  in
                       let uu____9076 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9048 uu____9076  in
                     let kwp =
                       let uu____9082 =
                         let uu____9091 =
                           FStar_Syntax_Syntax.null_binder post_k  in
                         [uu____9091]  in
                       let uu____9110 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9082 uu____9110  in
                     let post =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None post_k
                        in
                     let wp =
                       let uu____9117 =
                         let uu____9118 = FStar_Syntax_Syntax.mk_binder post
                            in
                         [uu____9118]  in
                       let uu____9137 =
                         let uu____9140 =
                           let uu____9147 =
                             FStar_TypeChecker_Env.get_range env  in
                           label FStar_TypeChecker_Err.exhaustiveness_check
                             uu____9147
                            in
                         let uu____9148 =
                           fvar_const env FStar_Parser_Const.false_lid  in
                         FStar_All.pipe_left uu____9140 uu____9148  in
                       FStar_Syntax_Util.abs uu____9117 uu____9137
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
                     let uu____9172 =
                       should_not_inline_whole_match ||
                         (let uu____9175 = is_pure_or_ghost_effect env eff
                             in
                          Prims.op_Negation uu____9175)
                        in
                     if uu____9172 then cthen true else cthen false  in
                   let branch_conditions =
                     let uu____9187 =
                       let uu____9200 =
                         let uu____9205 =
                           let uu____9216 =
                             FStar_All.pipe_right lcases
                               (FStar_List.map
                                  (fun uu____9260  ->
                                     match uu____9260 with
                                     | (g,uu____9275,uu____9276,uu____9277)
                                         -> g))
                              in
                           FStar_All.pipe_right uu____9216
                             (FStar_List.fold_left
                                (fun uu____9321  ->
                                   fun g  ->
                                     match uu____9321 with
                                     | (conds,acc) ->
                                         let cond =
                                           let uu____9362 =
                                             FStar_Syntax_Util.mk_neg g  in
                                           FStar_Syntax_Util.mk_conj acc
                                             uu____9362
                                            in
                                         ((FStar_List.append conds [cond]),
                                           cond))
                                ([FStar_Syntax_Util.t_true],
                                  FStar_Syntax_Util.t_true))
                            in
                         FStar_All.pipe_right uu____9205
                           FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____9200
                         (FStar_List.splitAt (FStar_List.length lcases))
                        in
                     FStar_All.pipe_right uu____9187
                       FStar_Pervasives_Native.fst
                      in
                   let uu____9463 =
                     FStar_List.fold_right2
                       (fun uu____9526  ->
                          fun bcond  ->
                            fun uu____9528  ->
                              match (uu____9526, uu____9528) with
                              | ((g,eff_label,uu____9588,cthen),(uu____9590,celse,g_comp))
                                  ->
                                  let uu____9637 =
                                    let uu____9642 =
                                      maybe_return eff_label cthen  in
                                    FStar_TypeChecker_Common.lcomp_comp
                                      uu____9642
                                     in
                                  (match uu____9637 with
                                   | (cthen1,gthen) ->
                                       let gthen1 =
                                         let uu____9654 =
                                           FStar_Syntax_Util.mk_conj bcond g
                                            in
                                         FStar_TypeChecker_Common.weaken_guard_formula
                                           gthen uu____9654
                                          in
                                       let uu____9655 =
                                         let uu____9666 =
                                           lift_comps_sep_guards env cthen1
                                             celse
                                             FStar_Pervasives_Native.None
                                             Lift_for_match
                                            in
                                         match uu____9666 with
                                         | (m,cthen2,celse1,g_lift_then,g_lift_else)
                                             ->
                                             let md =
                                               FStar_TypeChecker_Env.get_effect_decl
                                                 env m
                                                in
                                             let uu____9693 =
                                               FStar_All.pipe_right cthen2
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                in
                                             let uu____9694 =
                                               FStar_All.pipe_right celse1
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                in
                                             (md, uu____9693, uu____9694,
                                               g_lift_then, g_lift_else)
                                          in
                                       (match uu____9655 with
                                        | (md,ct_then,ct_else,g_lift_then,g_lift_else)
                                            ->
                                            let fn =
                                              let uu____9745 =
                                                FStar_All.pipe_right md
                                                  FStar_Syntax_Util.is_layered
                                                 in
                                              if uu____9745
                                              then mk_layered_conjunction
                                              else mk_non_layered_conjunction
                                               in
                                            let g_lift_then1 =
                                              let uu____9780 =
                                                FStar_Syntax_Util.mk_conj
                                                  bcond g
                                                 in
                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                g_lift_then uu____9780
                                               in
                                            let g_lift_else1 =
                                              let uu____9782 =
                                                let uu____9783 =
                                                  FStar_Syntax_Util.mk_neg g
                                                   in
                                                FStar_Syntax_Util.mk_conj
                                                  bcond uu____9783
                                                 in
                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                g_lift_else uu____9782
                                               in
                                            let g_lift =
                                              FStar_TypeChecker_Env.conj_guard
                                                g_lift_then1 g_lift_else1
                                               in
                                            let uu____9787 =
                                              let uu____9792 =
                                                FStar_TypeChecker_Env.get_range
                                                  env
                                                 in
                                              fn env md u_res_t res_t g
                                                ct_then ct_else uu____9792
                                               in
                                            (match uu____9787 with
                                             | (c,g_conjunction) ->
                                                 let uu____9803 =
                                                   FStar_TypeChecker_Env.conj_guards
                                                     [g_comp;
                                                     gthen1;
                                                     g_lift;
                                                     g_conjunction]
                                                    in
                                                 ((FStar_Pervasives_Native.Some
                                                     md), c, uu____9803)))))
                       lcases branch_conditions
                       (FStar_Pervasives_Native.None, default_case,
                         FStar_TypeChecker_Env.trivial_guard)
                      in
                   match uu____9463 with
                   | (md,comp,g_comp) ->
                       let g_comp1 =
                         let uu____9820 =
                           let uu____9821 =
                             FStar_All.pipe_right scrutinee
                               FStar_Syntax_Syntax.mk_binder
                              in
                           [uu____9821]  in
                         FStar_TypeChecker_Env.close_guard env0 uu____9820
                           g_comp
                          in
                       (match lcases with
                        | [] -> (comp, g_comp1)
                        | uu____9864::[] -> (comp, g_comp1)
                        | uu____9907 ->
                            let uu____9924 =
                              let uu____9926 =
                                FStar_All.pipe_right md FStar_Util.must  in
                              FStar_All.pipe_right uu____9926
                                FStar_Syntax_Util.is_layered
                               in
                            if uu____9924
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
                               let uu____9939 = destruct_wp_comp comp1  in
                               match uu____9939 with
                               | (uu____9950,uu____9951,wp) ->
                                   let ite_wp =
                                     let uu____9954 =
                                       FStar_All.pipe_right md1
                                         FStar_Syntax_Util.get_wp_ite_combinator
                                        in
                                     FStar_All.pipe_right uu____9954
                                       FStar_Util.must
                                      in
                                   let wp1 =
                                     let uu____9964 =
                                       let uu____9969 =
                                         FStar_TypeChecker_Env.inst_effect_fun_with
                                           [u_res_t] env md1 ite_wp
                                          in
                                       let uu____9970 =
                                         let uu____9971 =
                                           FStar_Syntax_Syntax.as_arg res_t
                                            in
                                         let uu____9980 =
                                           let uu____9991 =
                                             FStar_Syntax_Syntax.as_arg wp
                                              in
                                           [uu____9991]  in
                                         uu____9971 :: uu____9980  in
                                       FStar_Syntax_Syntax.mk_Tm_app
                                         uu____9969 uu____9970
                                        in
                                     uu____9964 FStar_Pervasives_Native.None
                                       wp.FStar_Syntax_Syntax.pos
                                      in
                                   let uu____10024 =
                                     mk_comp md1 u_res_t res_t wp1
                                       bind_cases_flags
                                      in
                                   (uu____10024, g_comp1))))
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
          let uu____10059 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____10059 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____10075 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____10081 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____10075 uu____10081
              else
                (let uu____10090 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____10096 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____10090 uu____10096)
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
          let uu____10121 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____10121
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____10124 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____10124
        then u_res
        else
          (let is_total =
             let uu____10131 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____10131
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____10142 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____10142 with
              | FStar_Pervasives_Native.None  ->
                  let uu____10145 =
                    let uu____10151 =
                      let uu____10153 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____10153
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____10151)
                     in
                  FStar_Errors.raise_error uu____10145
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
      let uu____10177 = destruct_wp_comp ct  in
      match uu____10177 with
      | (u_t,t,wp) ->
          let vc =
            let uu____10196 = FStar_TypeChecker_Env.get_range env  in
            let uu____10197 =
              let uu____10202 =
                let uu____10203 =
                  let uu____10204 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_trivial_combinator
                     in
                  FStar_All.pipe_right uu____10204 FStar_Util.must  in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____10203
                 in
              let uu____10211 =
                let uu____10212 = FStar_Syntax_Syntax.as_arg t  in
                let uu____10221 =
                  let uu____10232 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____10232]  in
                uu____10212 :: uu____10221  in
              FStar_Syntax_Syntax.mk_Tm_app uu____10202 uu____10211  in
            uu____10197 FStar_Pervasives_Native.None uu____10196  in
          let uu____10265 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____10265)
  
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
                  let uu____10320 =
                    FStar_TypeChecker_Env.try_lookup_lid env f  in
                  match uu____10320 with
                  | FStar_Pervasives_Native.Some uu____10335 ->
                      ((let uu____10353 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____10353
                        then
                          let uu____10357 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____10357
                        else ());
                       (let coercion =
                          let uu____10363 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____10363
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____10370 =
                            let uu____10371 =
                              let uu____10372 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10372
                               in
                            (FStar_Pervasives_Native.None, uu____10371)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____10370
                           in
                        let e1 =
                          let uu____10378 =
                            let uu____10383 =
                              let uu____10384 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____10384]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____10383
                             in
                          uu____10378 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____10418 =
                          let uu____10424 =
                            let uu____10426 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____10426
                             in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____10424)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____10418);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____10445 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10463 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10474 -> false 
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
      let uu____10498 = FStar_Syntax_Util.head_and_args t2  in
      match uu____10498 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____10543 =
              let uu____10558 =
                let uu____10559 = FStar_Syntax_Subst.compress h1  in
                uu____10559.FStar_Syntax_Syntax.n  in
              (uu____10558, args)  in
            match uu____10543 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____10606,uu____10607) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____10640) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match
               (uu____10661,branches),uu____10663) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc  ->
                        fun br  ->
                          match acc with
                          | Yes uu____10727 -> Maybe
                          | Maybe  -> Maybe
                          | No  ->
                              let uu____10728 =
                                FStar_Syntax_Subst.open_branch br  in
                              (match uu____10728 with
                               | (uu____10729,uu____10730,br_body) ->
                                   let uu____10748 =
                                     let uu____10749 =
                                       let uu____10754 =
                                         let uu____10755 =
                                           let uu____10758 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names
                                              in
                                           FStar_All.pipe_right uu____10758
                                             FStar_Util.set_elements
                                            in
                                         FStar_All.pipe_right uu____10755
                                           (FStar_TypeChecker_Env.push_bvs
                                              env)
                                          in
                                       check_erased uu____10754  in
                                     FStar_All.pipe_right br_body uu____10749
                                      in
                                   (match uu____10748 with
                                    | No  -> No
                                    | uu____10769 -> Maybe))) No)
            | uu____10770 -> No  in
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
            (((let uu____10822 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____10822) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____10841 =
                 let uu____10842 = FStar_Syntax_Subst.compress t1  in
                 uu____10842.FStar_Syntax_Syntax.n  in
               match uu____10841 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____10847 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____10857 =
                 let uu____10858 = FStar_Syntax_Subst.compress t1  in
                 uu____10858.FStar_Syntax_Syntax.n  in
               match uu____10857 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____10863 -> false  in
             let is_type t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let t2 = FStar_Syntax_Util.unrefine t1  in
               let uu____10874 =
                 let uu____10875 = FStar_Syntax_Subst.compress t2  in
                 uu____10875.FStar_Syntax_Syntax.n  in
               match uu____10874 with
               | FStar_Syntax_Syntax.Tm_type uu____10879 -> true
               | uu____10881 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____10884 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____10884 with
             | (head,args) ->
                 ((let uu____10934 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____10934
                   then
                     let uu____10938 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____10940 = FStar_Syntax_Print.term_to_string e
                        in
                     let uu____10942 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____10944 =
                       FStar_Syntax_Print.term_to_string exp_t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____10938 uu____10940 uu____10942 uu____10944
                   else ());
                  (let mk_erased u t =
                     let uu____10962 =
                       let uu____10965 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____10965 [u]  in
                     let uu____10966 =
                       let uu____10977 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____10977]  in
                     FStar_Syntax_Util.mk_app uu____10962 uu____10966  in
                   let uu____11002 =
                     let uu____11017 =
                       let uu____11018 = FStar_Syntax_Util.un_uinst head  in
                       uu____11018.FStar_Syntax_Syntax.n  in
                     (uu____11017, args)  in
                   match uu____11002 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type exp_t)
                       ->
                       let uu____11056 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____11056 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____11096 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11096 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11136 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11136 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11176 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11176 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____11197 ->
                       let uu____11212 =
                         let uu____11217 = check_erased env res_typ  in
                         let uu____11218 = check_erased env exp_t  in
                         (uu____11217, uu____11218)  in
                       (match uu____11212 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11227 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____11227 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____11238 =
                                   let uu____11243 =
                                     let uu____11244 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____11244]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____11243
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____11238 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11279 =
                              let uu____11284 =
                                let uu____11285 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____11285]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____11284
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____11279 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____11318 ->
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
        let uu____11353 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____11353 with
        | (hd,args) ->
            let uu____11402 =
              let uu____11417 =
                let uu____11418 = FStar_Syntax_Subst.compress hd  in
                uu____11418.FStar_Syntax_Syntax.n  in
              (uu____11417, args)  in
            (match uu____11402 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____11456 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun uu____11483  ->
                      FStar_Pervasives_Native.Some uu____11483) uu____11456
             | uu____11484 -> FStar_Pervasives_Native.None)
  
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
          (let uu____11537 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____11537
           then
             let uu____11540 = FStar_Syntax_Print.term_to_string e  in
             let uu____11542 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____11544 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____11540 uu____11542 uu____11544
           else ());
          (let use_eq =
             (env.FStar_TypeChecker_Env.use_eq_strict ||
                env.FStar_TypeChecker_Env.use_eq)
               ||
               (let uu____11554 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____11554 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____11579 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____11605 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____11605, false)
             else
               (let uu____11615 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____11615, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____11628) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____11640 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____11640
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1359_11656 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1359_11656.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1359_11656.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1359_11656.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard) ->
               let uu____11663 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____11663 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____11679 =
                      let uu____11680 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____11680 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____11700 =
                            let uu____11702 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____11702 = FStar_Syntax_Util.Equal  in
                          if uu____11700
                          then
                            ((let uu____11709 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____11709
                              then
                                let uu____11713 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____11715 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____11713 uu____11715
                              else ());
                             (let uu____11720 = set_result_typ c  in
                              (uu____11720, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____11727 ->
                                   true
                               | uu____11735 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____11744 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____11744
                                  in
                               let lc1 =
                                 let uu____11746 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____11747 =
                                   let uu____11748 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____11748)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____11746 uu____11747
                                  in
                               ((let uu____11752 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____11752
                                 then
                                   let uu____11756 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____11758 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____11760 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____11762 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____11756 uu____11758 uu____11760
                                     uu____11762
                                 else ());
                                (let uu____11767 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____11767 with
                                 | (c1,g_lc) ->
                                     let uu____11778 = set_result_typ c1  in
                                     let uu____11779 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____11778, uu____11779)))
                             else
                               ((let uu____11783 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____11783
                                 then
                                   let uu____11787 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____11789 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____11787 uu____11789
                                 else ());
                                (let uu____11794 = set_result_typ c  in
                                 (uu____11794, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1396_11798 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1396_11798.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1396_11798.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1396_11798.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____11808 =
                      let uu____11809 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____11809
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____11819 =
                           let uu____11820 = FStar_Syntax_Subst.compress f1
                              in
                           uu____11820.FStar_Syntax_Syntax.n  in
                         match uu____11819 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____11827,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____11829;
                                            FStar_Syntax_Syntax.vars =
                                              uu____11830;_},uu____11831)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1412_11857 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1412_11857.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1412_11857.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1412_11857.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____11858 ->
                             let uu____11859 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____11859 with
                              | (c,g_c) ->
                                  ((let uu____11871 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____11871
                                    then
                                      let uu____11875 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____11877 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____11879 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____11881 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____11875 uu____11877 uu____11879
                                        uu____11881
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
                                        let uu____11894 =
                                          let uu____11899 =
                                            let uu____11900 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____11900]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____11899
                                           in
                                        uu____11894
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____11927 =
                                      let uu____11932 =
                                        FStar_All.pipe_left
                                          (fun uu____11953  ->
                                             FStar_Pervasives_Native.Some
                                               uu____11953)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____11954 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____11955 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____11956 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____11932
                                        uu____11954 e uu____11955 uu____11956
                                       in
                                    match uu____11927 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1430_11964 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1430_11964.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1430_11964.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____11966 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____11966
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____11969 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____11969 with
                                         | (c2,g_lc) ->
                                             ((let uu____11981 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____11981
                                               then
                                                 let uu____11985 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____11985
                                               else ());
                                              (let uu____11990 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____11990))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_11999  ->
                              match uu___6_11999 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____12002 -> []))
                       in
                    let lc1 =
                      let uu____12004 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____12004 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1446_12006 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1446_12006.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1446_12006.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1446_12006.FStar_TypeChecker_Common.implicits)
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
        let uu____12042 =
          let uu____12045 =
            let uu____12050 =
              let uu____12051 =
                let uu____12060 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____12060  in
              [uu____12051]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____12050  in
          uu____12045 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____12042  in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____12083 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____12083
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____12102 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____12118 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____12135 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____12135
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____12151)::(ens,uu____12153)::uu____12154 ->
                    let uu____12197 =
                      let uu____12200 = norm req  in
                      FStar_Pervasives_Native.Some uu____12200  in
                    let uu____12201 =
                      let uu____12202 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm uu____12202  in
                    (uu____12197, uu____12201)
                | uu____12205 ->
                    let uu____12216 =
                      let uu____12222 =
                        let uu____12224 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____12224
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____12222)
                       in
                    FStar_Errors.raise_error uu____12216
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____12244)::uu____12245 ->
                    let uu____12272 =
                      let uu____12277 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____12277
                       in
                    (match uu____12272 with
                     | (us_r,uu____12309) ->
                         let uu____12310 =
                           let uu____12315 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____12315
                            in
                         (match uu____12310 with
                          | (us_e,uu____12347) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____12350 =
                                  let uu____12351 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12351
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12350
                                  us_r
                                 in
                              let as_ens =
                                let uu____12353 =
                                  let uu____12354 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12354
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12353
                                  us_e
                                 in
                              let req =
                                let uu____12358 =
                                  let uu____12363 =
                                    let uu____12364 =
                                      let uu____12375 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12375]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12364
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____12363
                                   in
                                uu____12358 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____12415 =
                                  let uu____12420 =
                                    let uu____12421 =
                                      let uu____12432 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12432]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12421
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____12420
                                   in
                                uu____12415 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____12469 =
                                let uu____12472 = norm req  in
                                FStar_Pervasives_Native.Some uu____12472  in
                              let uu____12473 =
                                let uu____12474 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm uu____12474  in
                              (uu____12469, uu____12473)))
                | uu____12477 -> failwith "Impossible"))
  
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
        (let uu____12516 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____12516
         then
           let uu____12521 = FStar_Syntax_Print.term_to_string tm  in
           let uu____12523 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____12521
             uu____12523
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
          (let uu____12582 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____12582
           then
             let uu____12587 = FStar_Syntax_Print.term_to_string tm  in
             let uu____12589 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____12587
               uu____12589
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____12600 =
      let uu____12602 =
        let uu____12603 = FStar_Syntax_Subst.compress t  in
        uu____12603.FStar_Syntax_Syntax.n  in
      match uu____12602 with
      | FStar_Syntax_Syntax.Tm_app uu____12607 -> false
      | uu____12625 -> true  in
    if uu____12600
    then t
    else
      (let uu____12630 = FStar_Syntax_Util.head_and_args t  in
       match uu____12630 with
       | (head,args) ->
           let uu____12673 =
             let uu____12675 =
               let uu____12676 = FStar_Syntax_Subst.compress head  in
               uu____12676.FStar_Syntax_Syntax.n  in
             match uu____12675 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____12681 -> false  in
           if uu____12673
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____12713 ->
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
          ((let uu____12760 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____12760
            then
              let uu____12763 = FStar_Syntax_Print.term_to_string e  in
              let uu____12765 = FStar_Syntax_Print.term_to_string t  in
              let uu____12767 =
                let uu____12769 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____12769
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____12763 uu____12765 uu____12767
            else ());
           (let unfolded_arrow_formals t1 =
              let rec aux bs t2 =
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf env t2  in
                let uu____12805 = FStar_Syntax_Util.arrow_formals t3  in
                match uu____12805 with
                | (bs',t4) ->
                    (match bs' with
                     | [] -> bs
                     | bs'1 -> aux (FStar_List.append bs bs'1) t4)
                 in
              aux [] t1  in
            let number_of_implicits t1 =
              let formals = unfolded_arrow_formals t1  in
              let n_implicits =
                let uu____12839 =
                  FStar_All.pipe_right formals
                    (FStar_Util.prefix_until
                       (fun uu____12917  ->
                          match uu____12917 with
                          | (uu____12925,imp) ->
                              (FStar_Option.isNone imp) ||
                                (let uu____12932 =
                                   FStar_Syntax_Util.eq_aqual imp
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Equality)
                                    in
                                 uu____12932 = FStar_Syntax_Util.Equal)))
                   in
                match uu____12839 with
                | FStar_Pervasives_Native.None  -> FStar_List.length formals
                | FStar_Pervasives_Native.Some
                    (implicits,_first_explicit,_rest) ->
                    FStar_List.length implicits
                 in
              n_implicits  in
            let inst_n_binders t1 =
              let uu____13051 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____13051 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____13065 =
                      let uu____13071 =
                        let uu____13073 = FStar_Util.string_of_int n_expected
                           in
                        let uu____13075 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____13077 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____13073 uu____13075 uu____13077
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____13071)
                       in
                    let uu____13081 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____13065 uu____13081
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_13099 =
              match uu___7_13099 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____13142 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____13142 with
                 | (bs1,c1) ->
                     let rec aux subst inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some
                          uu____13273,uu____13260) when
                           uu____13273 = Prims.int_zero ->
                           ([], bs2, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____13306,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____13308))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____13342 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____13342 with
                            | (v,uu____13383,g) ->
                                ((let uu____13398 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13398
                                  then
                                    let uu____13401 =
                                      FStar_Syntax_Print.term_to_string v  in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____13401
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst
                                     in
                                  let uu____13411 =
                                    aux subst1 (decr_inst inst_n) rest  in
                                  match uu____13411 with
                                  | (args,bs3,subst2,g') ->
                                      let uu____13504 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____13504))))
                       | (uu____13531,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____13568 =
                             let uu____13581 =
                               let uu____13588 =
                                 let uu____13593 = FStar_Dyn.mkdyn env  in
                                 (uu____13593, tau)  in
                               FStar_Pervasives_Native.Some uu____13588  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____13581
                              in
                           (match uu____13568 with
                            | (v,uu____13626,g) ->
                                ((let uu____13641 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13641
                                  then
                                    let uu____13644 =
                                      FStar_Syntax_Print.term_to_string v  in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____13644
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst
                                     in
                                  let uu____13654 =
                                    aux subst1 (decr_inst inst_n) rest  in
                                  match uu____13654 with
                                  | (args,bs3,subst2,g') ->
                                      let uu____13747 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____13747))))
                       | (uu____13774,bs3) ->
                           ([], bs3, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____13822 =
                       let uu____13849 = inst_n_binders t1  in
                       aux [] uu____13849 bs1  in
                     (match uu____13822 with
                      | (args,bs2,subst,guard) ->
                          (match (args, bs2) with
                           | ([],uu____13921) -> (e, torig, guard)
                           | (uu____13952,[]) when
                               let uu____13983 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____13983 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____13985 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____14013 ->
                                     FStar_Syntax_Util.arrow bs2 c1
                                  in
                               let t3 = FStar_Syntax_Subst.subst subst t2  in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   FStar_Pervasives_Native.None
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               (e1, t3, guard))))
            | uu____14026 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs  ->
    let uu____14038 =
      let uu____14042 = FStar_Util.set_elements univs  in
      FStar_All.pipe_right uu____14042
        (FStar_List.map
           (fun u  ->
              let uu____14054 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____14054 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____14038 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____14082 = FStar_Util.set_is_empty x  in
      if uu____14082
      then []
      else
        (let s =
           let uu____14102 =
             let uu____14105 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____14105  in
           FStar_All.pipe_right uu____14102 FStar_Util.set_elements  in
         (let uu____14123 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____14123
          then
            let uu____14128 =
              let uu____14130 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____14130  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____14128
          else ());
         (let r =
            let uu____14139 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____14139  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____14184 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____14184
                     then
                       let uu____14189 =
                         let uu____14191 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____14191
                          in
                       let uu____14195 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____14197 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____14189 uu____14195 uu____14197
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
        let uu____14227 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____14227 FStar_Util.set_elements  in
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
        | ([],uu____14266) -> generalized_univ_names
        | (uu____14273,[]) -> explicit_univ_names
        | uu____14280 ->
            let uu____14289 =
              let uu____14295 =
                let uu____14297 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____14297
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____14295)
               in
            FStar_Errors.raise_error uu____14289 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____14319 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____14319
       then
         let uu____14324 = FStar_Syntax_Print.term_to_string t  in
         let uu____14326 = FStar_Syntax_Print.univ_names_to_string univnames
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____14324 uu____14326
       else ());
      (let univs = FStar_Syntax_Free.univs t  in
       (let uu____14335 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____14335
        then
          let uu____14340 = string_of_univs univs  in
          FStar_Util.print1 "univs to gen : %s\n" uu____14340
        else ());
       (let gen = gen_univs env univs  in
        (let uu____14349 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____14349
         then
           let uu____14354 = FStar_Syntax_Print.term_to_string t  in
           let uu____14356 = FStar_Syntax_Print.univ_names_to_string gen  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____14354 uu____14356
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
        let uu____14440 =
          let uu____14442 =
            FStar_Util.for_all
              (fun uu____14456  ->
                 match uu____14456 with
                 | (uu____14466,uu____14467,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____14442  in
        if uu____14440
        then FStar_Pervasives_Native.None
        else
          (let norm c =
             (let uu____14519 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____14519
              then
                let uu____14522 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____14522
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____14529 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____14529
               then
                 let uu____14532 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____14532
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____14550 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____14550 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____14584 =
             match uu____14584 with
             | (lbname,e,c) ->
                 let c1 = norm c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____14621 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____14621
                   then
                     let uu____14626 =
                       let uu____14628 =
                         let uu____14632 = FStar_Util.set_elements univs  in
                         FStar_All.pipe_right uu____14632
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____14628
                         (FStar_String.concat ", ")
                        in
                     let uu____14688 =
                       let uu____14690 =
                         let uu____14694 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____14694
                           (FStar_List.map
                              (fun u  ->
                                 let uu____14707 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____14709 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____14707
                                   uu____14709))
                          in
                       FStar_All.pipe_right uu____14690
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____14626
                       uu____14688
                   else ());
                  (let univs1 =
                     let uu____14723 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs1  ->
                          fun uv  ->
                            let uu____14735 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs1 uu____14735) univs
                       uu____14723
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____14742 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____14742
                    then
                      let uu____14747 =
                        let uu____14749 =
                          let uu____14753 = FStar_Util.set_elements univs1
                             in
                          FStar_All.pipe_right uu____14753
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____14749
                          (FStar_String.concat ", ")
                         in
                      let uu____14809 =
                        let uu____14811 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____14825 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____14827 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____14825
                                    uu____14827))
                           in
                        FStar_All.pipe_right uu____14811
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____14747 uu____14809
                    else ());
                   (univs1, uvs, (lbname, e, c1))))
              in
           let uu____14848 =
             let uu____14865 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____14865  in
           match uu____14848 with
           | (univs,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____14955 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____14955
                 then ()
                 else
                   (let uu____14960 = lec_hd  in
                    match uu____14960 with
                    | (lb1,uu____14968,uu____14969) ->
                        let uu____14970 = lec2  in
                        (match uu____14970 with
                         | (lb2,uu____14978,uu____14979) ->
                             let msg =
                               let uu____14982 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____14984 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____14982 uu____14984
                                in
                             let uu____14987 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____14987))
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
                 let uu____15055 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____15055
                 then ()
                 else
                   (let uu____15060 = lec_hd  in
                    match uu____15060 with
                    | (lb1,uu____15068,uu____15069) ->
                        let uu____15070 = lec2  in
                        (match uu____15070 with
                         | (lb2,uu____15078,uu____15079) ->
                             let msg =
                               let uu____15082 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15084 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____15082 uu____15084
                                in
                             let uu____15087 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____15087))
                  in
               let lecs1 =
                 let uu____15098 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____15151 = univs_and_uvars_of_lec this_lec  in
                        match uu____15151 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____15098 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail rng k =
                   let uu____15261 = lec_hd  in
                   match uu____15261 with
                   | (lbname,e,c) ->
                       let uu____15271 =
                         let uu____15277 =
                           let uu____15279 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____15281 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____15283 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____15279 uu____15281 uu____15283
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____15277)
                          in
                       FStar_Errors.raise_error uu____15271 rng
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____15305 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____15305 with
                         | FStar_Pervasives_Native.Some uu____15314 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____15322 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____15326 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____15326 with
                              | (bs,kres) ->
                                  ((let uu____15346 =
                                      let uu____15347 =
                                        let uu____15350 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____15350
                                         in
                                      uu____15347.FStar_Syntax_Syntax.n  in
                                    match uu____15346 with
                                    | FStar_Syntax_Syntax.Tm_type uu____15351
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____15355 =
                                          let uu____15357 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____15357  in
                                        if uu____15355
                                        then
                                          fail
                                            u.FStar_Syntax_Syntax.ctx_uvar_range
                                            kres
                                        else ()
                                    | uu____15362 ->
                                        fail
                                          u.FStar_Syntax_Syntax.ctx_uvar_range
                                          kres);
                                   (let a =
                                      let uu____15364 =
                                        let uu____15367 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun uu____15370  ->
                                             FStar_Pervasives_Native.Some
                                               uu____15370) uu____15367
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____15364
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____15378 ->
                                          let uu____15379 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____15379
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
                      (fun uu____15482  ->
                         match uu____15482 with
                         | (lbname,e,c) ->
                             let uu____15528 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____15589 ->
                                   let uu____15602 = (e, c)  in
                                   (match uu____15602 with
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
                                                (fun uu____15642  ->
                                                   match uu____15642 with
                                                   | (x,uu____15648) ->
                                                       let uu____15649 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____15649)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____15667 =
                                                let uu____15669 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____15669
                                                 in
                                              if uu____15667
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
                                          let uu____15678 =
                                            let uu____15679 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____15679.FStar_Syntax_Syntax.n
                                             in
                                          match uu____15678 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____15704 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____15704 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____15715 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____15719 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____15719, gen_tvars))
                                in
                             (match uu____15528 with
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
        (let uu____15866 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____15866
         then
           let uu____15869 =
             let uu____15871 =
               FStar_List.map
                 (fun uu____15886  ->
                    match uu____15886 with
                    | (lb,uu____15895,uu____15896) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____15871 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____15869
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____15922  ->
                match uu____15922 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____15951 = gen env is_rec lecs  in
           match uu____15951 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____16050  ->
                       match uu____16050 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____16112 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____16112
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____16160  ->
                           match uu____16160 with
                           | (l,us,e,c,gvs) ->
                               let uu____16194 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____16196 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____16198 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____16200 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____16202 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____16194 uu____16196 uu____16198
                                 uu____16200 uu____16202))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames  ->
              fun uu____16247  ->
                match uu____16247 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____16291 =
                      check_universe_generalization univnames
                        generalized_univs t
                       in
                    (l, uu____16291, t, c, gvs)) univnames_lecs
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
        let uu____16346 =
          let uu____16350 =
            let uu____16352 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____16352  in
          FStar_Pervasives_Native.Some uu____16350  in
        FStar_Profiling.profile
          (fun uu____16369  -> generalize' env is_rec lecs) uu____16346
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
              let uu____16426 =
                FStar_TypeChecker_Rel.get_teq_predicate env2 t1 t21  in
              match uu____16426 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some f ->
                  let uu____16432 = FStar_TypeChecker_Env.apply_guard f e  in
                  FStar_All.pipe_right uu____16432
                    (fun uu____16435  ->
                       FStar_Pervasives_Native.Some uu____16435)
            else
              if env2.FStar_TypeChecker_Env.use_eq
              then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
              else
                (let uu____16444 =
                   FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                    in
                 match uu____16444 with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some f ->
                     let uu____16450 = FStar_TypeChecker_Env.apply_guard f e
                        in
                     FStar_All.pipe_left
                       (fun uu____16453  ->
                          FStar_Pervasives_Native.Some uu____16453)
                       uu____16450)
             in
          let uu____16454 = maybe_coerce_lc env1 e lc t2  in
          match uu____16454 with
          | (e1,lc1,g_c) ->
              let uu____16470 =
                check env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____16470 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16479 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____16485 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____16479 uu____16485
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____16494 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____16494
                     then
                       let uu____16499 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____16499
                     else ());
                    (let uu____16505 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (e1, lc1, uu____16505))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____16533 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____16533
         then
           let uu____16536 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____16536
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____16550 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____16550 with
         | (c,g_c) ->
             let uu____16562 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____16562
             then
               let uu____16570 =
                 let uu____16572 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____16572  in
               (uu____16570, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____16580 =
                    let uu____16581 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____16581
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____16580
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____16582 = check_trivial_precondition env c1  in
                match uu____16582 with
                | (ct,vc,g_pre) ->
                    ((let uu____16598 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____16598
                      then
                        let uu____16603 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____16603
                      else ());
                     (let uu____16608 =
                        let uu____16610 =
                          let uu____16611 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____16611  in
                        discharge uu____16610  in
                      let uu____16612 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____16608, uu____16612)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head  ->
    fun seen_args  ->
      let short_bin_op f uu___8_16646 =
        match uu___8_16646 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst,uu____16656)::[] -> f fst
        | uu____16681 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____16693 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____16693
          (fun uu____16694  ->
             FStar_TypeChecker_Common.NonTrivial uu____16694)
         in
      let op_or_e e =
        let uu____16705 =
          let uu____16706 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____16706  in
        FStar_All.pipe_right uu____16705
          (fun uu____16709  ->
             FStar_TypeChecker_Common.NonTrivial uu____16709)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun uu____16716  ->
             FStar_TypeChecker_Common.NonTrivial uu____16716)
         in
      let op_or_t t =
        let uu____16727 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____16727
          (fun uu____16730  ->
             FStar_TypeChecker_Common.NonTrivial uu____16730)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun uu____16737  ->
             FStar_TypeChecker_Common.NonTrivial uu____16737)
         in
      let short_op_ite uu___9_16743 =
        match uu___9_16743 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____16753)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____16780)::[] ->
            let uu____16821 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____16821
              (fun uu____16822  ->
                 FStar_TypeChecker_Common.NonTrivial uu____16822)
        | uu____16823 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____16835 =
          let uu____16843 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____16843)  in
        let uu____16851 =
          let uu____16861 =
            let uu____16869 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____16869)  in
          let uu____16877 =
            let uu____16887 =
              let uu____16895 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____16895)  in
            let uu____16903 =
              let uu____16913 =
                let uu____16921 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____16921)  in
              let uu____16929 =
                let uu____16939 =
                  let uu____16947 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____16947)  in
                [uu____16939; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____16913 :: uu____16929  in
            uu____16887 :: uu____16903  in
          uu____16861 :: uu____16877  in
        uu____16835 :: uu____16851  in
      match head.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____17009 =
            FStar_Util.find_map table
              (fun uu____17024  ->
                 match uu____17024 with
                 | (x,mk) ->
                     let uu____17041 = FStar_Ident.lid_equals x lid  in
                     if uu____17041
                     then
                       let uu____17046 = mk seen_args  in
                       FStar_Pervasives_Native.Some uu____17046
                     else FStar_Pervasives_Native.None)
             in
          (match uu____17009 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____17050 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____17058 =
      let uu____17059 = FStar_Syntax_Util.un_uinst l  in
      uu____17059.FStar_Syntax_Syntax.n  in
    match uu____17058 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____17064 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd,uu____17100)::uu____17101 -> FStar_Syntax_Syntax.range_of_bv hd
        | uu____17120 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____17129,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____17130))::uu____17131 -> bs
      | uu____17149 ->
          let uu____17150 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____17150 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____17154 =
                 let uu____17155 = FStar_Syntax_Subst.compress t  in
                 uu____17155.FStar_Syntax_Syntax.n  in
               (match uu____17154 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____17159) ->
                    let uu____17180 =
                      FStar_Util.prefix_until
                        (fun uu___10_17220  ->
                           match uu___10_17220 with
                           | (uu____17228,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____17229)) ->
                               false
                           | uu____17234 -> true) bs'
                       in
                    (match uu____17180 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____17270,uu____17271) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____17343,uu____17344) ->
                         let uu____17417 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____17438  ->
                                   match uu____17438 with
                                   | (x,uu____17447) ->
                                       let uu____17452 =
                                         FStar_Ident.text_of_id
                                           x.FStar_Syntax_Syntax.ppname
                                          in
                                       FStar_Util.starts_with uu____17452 "'"))
                            in
                         if uu____17417
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____17498  ->
                                     match uu____17498 with
                                     | (x,i) ->
                                         let uu____17517 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____17517, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____17528 -> bs))
  
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
            let uu____17557 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____17557
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
          let uu____17588 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____17588
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
        (let uu____17631 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____17631
         then
           ((let uu____17636 = FStar_Ident.string_of_lid lident  in
             d uu____17636);
            (let uu____17638 = FStar_Ident.string_of_lid lident  in
             let uu____17640 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____17638 uu____17640))
         else ());
        (let fv =
           let uu____17646 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____17646
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
         let uu____17658 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___2068_17660 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2068_17660.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2068_17660.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2068_17660.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2068_17660.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2068_17660.FStar_Syntax_Syntax.sigopts)
           }), uu____17658))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_17678 =
        match uu___11_17678 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____17681 -> false  in
      let reducibility uu___12_17689 =
        match uu___12_17689 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____17696 -> false  in
      let assumption uu___13_17704 =
        match uu___13_17704 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____17708 -> false  in
      let reification uu___14_17716 =
        match uu___14_17716 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____17719 -> true
        | uu____17721 -> false  in
      let inferred uu___15_17729 =
        match uu___15_17729 with
        | FStar_Syntax_Syntax.Discriminator uu____17731 -> true
        | FStar_Syntax_Syntax.Projector uu____17733 -> true
        | FStar_Syntax_Syntax.RecordType uu____17739 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____17749 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____17762 -> false  in
      let has_eq uu___16_17770 =
        match uu___16_17770 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____17774 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____17853 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____17860 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____17893 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____17893))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____17924 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____17924
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
           | FStar_Syntax_Syntax.Sig_bundle uu____17944 ->
               let uu____17953 =
                 let uu____17955 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_17961  ->
                           match uu___17_17961 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____17964 -> false))
                    in
                 Prims.op_Negation uu____17955  in
               if uu____17953
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____17971 -> ()
           | FStar_Syntax_Syntax.Sig_fail uu____17978 -> ()
           | uu____17991 ->
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
      let uu____18005 =
        let uu____18007 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_18013  ->
                  match uu___18_18013 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____18016 -> false))
           in
        FStar_All.pipe_right uu____18007 Prims.op_Negation  in
      if uu____18005
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____18037 =
            let uu____18043 =
              let uu____18045 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____18045 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____18043)  in
          FStar_Errors.raise_error uu____18037 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____18063 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____18071 =
            let uu____18073 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____18073  in
          if uu____18071 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____18084),uu____18085) ->
              ((let uu____18097 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____18097
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____18106 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____18106
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____18117 ->
              ((let uu____18127 =
                  let uu____18129 =
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
                  Prims.op_Negation uu____18129  in
                if uu____18127 then err'1 () else ());
               (let uu____18139 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_18145  ->
                           match uu___19_18145 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____18148 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____18139
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____18154 ->
              let uu____18161 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____18161 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____18169 ->
              let uu____18176 =
                let uu____18178 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____18178  in
              if uu____18176 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____18188 ->
              let uu____18189 =
                let uu____18191 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____18191  in
              if uu____18189 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18201 ->
              let uu____18214 =
                let uu____18216 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____18216  in
              if uu____18214 then err'1 () else ()
          | uu____18226 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____18265 =
          let uu____18266 = FStar_Syntax_Subst.compress t1  in
          uu____18266.FStar_Syntax_Syntax.n  in
        match uu____18265 with
        | FStar_Syntax_Syntax.Tm_arrow uu____18270 ->
            let uu____18285 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____18285 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____18294;
               FStar_Syntax_Syntax.index = uu____18295;
               FStar_Syntax_Syntax.sort = t2;_},uu____18297)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head,uu____18306) -> descend env head
        | FStar_Syntax_Syntax.Tm_uinst (head,uu____18332) -> descend env head
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____18338 -> false
      
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
        (let uu____18348 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____18348
         then
           let uu____18353 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____18353
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
                  let uu____18418 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____18418 r  in
                let uu____18428 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____18428 with
                | (uu____18437,signature) ->
                    let uu____18439 =
                      let uu____18440 = FStar_Syntax_Subst.compress signature
                         in
                      uu____18440.FStar_Syntax_Syntax.n  in
                    (match uu____18439 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18448) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____18496 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____18512 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____18514 =
                                       FStar_Ident.string_of_lid eff_name  in
                                     let uu____18516 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____18512 uu____18514 uu____18516) r
                                 in
                              (match uu____18496 with
                               | (is,g) ->
                                   let uu____18529 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____18531 =
                                             let uu____18532 =
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
                                                 = uu____18532;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____18531
                                            in
                                         let uu____18551 =
                                           let uu____18558 =
                                             let uu____18559 =
                                               let uu____18574 =
                                                 let uu____18583 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_unit
                                                    in
                                                 [uu____18583]  in
                                               (uu____18574, eff_c)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____18559
                                              in
                                           FStar_Syntax_Syntax.mk uu____18558
                                            in
                                         uu____18551
                                           FStar_Pervasives_Native.None r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____18614 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____18614
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____18623 =
                                           let uu____18628 =
                                             FStar_List.map
                                               FStar_Syntax_Syntax.as_arg
                                               (a_tm :: is)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____18628
                                            in
                                         uu____18623
                                           FStar_Pervasives_Native.None r
                                      in
                                   (uu____18529, g))
                          | uu____18637 -> fail signature)
                     | uu____18638 -> fail signature)
  
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
            let uu____18669 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____18669
              (fun ed  ->
                 let uu____18677 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____18677 u a_tm)
  
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
              let uu____18713 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____18713 with
              | (uu____18718,sig_tm) ->
                  let fail t =
                    let uu____18726 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____18726 r  in
                  let uu____18732 =
                    let uu____18733 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____18733.FStar_Syntax_Syntax.n  in
                  (match uu____18732 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18737) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____18760)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____18782 -> fail sig_tm)
                   | uu____18783 -> fail sig_tm)
  
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
          (let uu____18814 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____18814
           then
             let uu____18819 = FStar_Syntax_Print.comp_to_string c  in
             let uu____18821 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____18819 uu____18821
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____18828 =
             let uu____18839 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____18840 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____18839, (ct.FStar_Syntax_Syntax.result_typ), uu____18840)
              in
           match uu____18828 with
           | (u,a,c_is) ->
               let uu____18888 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____18888 with
                | (uu____18897,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____18908 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____18910 = FStar_Ident.string_of_lid tgt  in
                      let uu____18912 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____18908 uu____18910 s uu____18912
                       in
                    let uu____18915 =
                      let uu____18948 =
                        let uu____18949 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____18949.FStar_Syntax_Syntax.n  in
                      match uu____18948 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____19013 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____19013 with
                           | (a_b::bs1,c2) ->
                               let uu____19073 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               (a_b, uu____19073, c2))
                      | uu____19161 ->
                          let uu____19162 =
                            let uu____19168 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____19168)
                             in
                          FStar_Errors.raise_error uu____19162 r
                       in
                    (match uu____18915 with
                     | (a_b,(rest_bs,f_b::[]),lift_c) ->
                         let uu____19286 =
                           let uu____19293 =
                             let uu____19294 =
                               let uu____19295 =
                                 let uu____19302 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____19302, a)  in
                               FStar_Syntax_Syntax.NT uu____19295  in
                             [uu____19294]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____19293
                             (fun b  ->
                                let uu____19319 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____19321 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____19323 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____19325 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____19319 uu____19321 uu____19323
                                  uu____19325) r
                            in
                         (match uu____19286 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____19339 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____19339
                                then
                                  let uu____19344 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____19353 =
                                             let uu____19355 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____19355
                                              in
                                           Prims.op_Hat s uu____19353) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____19344
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____19386 =
                                           let uu____19393 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____19393, t)  in
                                         FStar_Syntax_Syntax.NT uu____19386)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____19412 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____19412
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____19418 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
                                    FStar_Syntax_Util.effect_indices_from_repr
                                      f_sort uu____19418 r ""
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____19428 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____19428)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let lift_ct =
                                  let uu____19430 =
                                    FStar_All.pipe_right lift_c
                                      (FStar_Syntax_Subst.subst_comp substs)
                                     in
                                  FStar_All.pipe_right uu____19430
                                    FStar_Syntax_Util.comp_to_comp_typ
                                   in
                                let is =
                                  let uu____19434 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  FStar_Syntax_Util.effect_indices_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____19434 r ""
                                   in
                                let fml =
                                  let uu____19440 =
                                    let uu____19445 =
                                      FStar_List.hd
                                        lift_ct.FStar_Syntax_Syntax.comp_univs
                                       in
                                    let uu____19446 =
                                      let uu____19447 =
                                        FStar_List.hd
                                          lift_ct.FStar_Syntax_Syntax.effect_args
                                         in
                                      FStar_Pervasives_Native.fst uu____19447
                                       in
                                    (uu____19445, uu____19446)  in
                                  match uu____19440 with
                                  | (u1,wp) ->
                                      FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                        env u1
                                        lift_ct.FStar_Syntax_Syntax.result_typ
                                        wp FStar_Range.dummyRange
                                   in
                                (let uu____19473 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects"))
                                     &&
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme)
                                    in
                                 if uu____19473
                                 then
                                   let uu____19479 =
                                     FStar_Syntax_Print.term_to_string fml
                                      in
                                   FStar_Util.print1 "Guard for lift is: %s"
                                     uu____19479
                                 else ());
                                (let c1 =
                                   let uu____19485 =
                                     let uu____19486 =
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
                                         uu____19486;
                                       FStar_Syntax_Syntax.flags = []
                                     }  in
                                   FStar_Syntax_Syntax.mk_Comp uu____19485
                                    in
                                 (let uu____19510 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects")
                                     in
                                  if uu____19510
                                  then
                                    let uu____19515 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    FStar_Util.print1 "} Lifted comp: %s\n"
                                      uu____19515
                                  else ());
                                 (let uu____19520 =
                                    let uu____19521 =
                                      FStar_TypeChecker_Env.conj_guard g
                                        guard_f
                                       in
                                    let uu____19522 =
                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                        (FStar_TypeChecker_Common.NonTrivial
                                           fml)
                                       in
                                    FStar_TypeChecker_Env.conj_guard
                                      uu____19521 uu____19522
                                     in
                                  (c1, uu____19520)))))))))
  
let lift_tf_layered_effect_term :
  'uuuuuu19536 .
    'uuuuuu19536 ->
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
              let uu____19565 =
                let uu____19570 =
                  FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____19570
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____19565 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____19613 =
                let uu____19614 =
                  let uu____19617 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____19617
                    FStar_Syntax_Subst.compress
                   in
                uu____19614.FStar_Syntax_Syntax.n  in
              match uu____19613 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____19640::bs,uu____19642)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____19682 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____19682
                    FStar_Pervasives_Native.fst
              | uu____19788 ->
                  let uu____19789 =
                    let uu____19795 =
                      let uu____19797 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____19797
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____19795)  in
                  FStar_Errors.raise_error uu____19789
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____19824 = FStar_Syntax_Syntax.as_arg a  in
              let uu____19833 =
                let uu____19844 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____19880  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____19887 =
                  let uu____19898 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____19898]  in
                FStar_List.append uu____19844 uu____19887  in
              uu____19824 :: uu____19833  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index  ->
        let uu____19969 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____19969 with
        | (uu____19974,t) ->
            let err n =
              let uu____19984 =
                let uu____19990 =
                  let uu____19992 = FStar_Ident.string_of_lid datacon  in
                  let uu____19994 = FStar_Util.string_of_int n  in
                  let uu____19996 = FStar_Util.string_of_int index  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____19992 uu____19994 uu____19996
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____19990)
                 in
              let uu____20000 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____19984 uu____20000  in
            let uu____20001 =
              let uu____20002 = FStar_Syntax_Subst.compress t  in
              uu____20002.FStar_Syntax_Syntax.n  in
            (match uu____20001 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____20006) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____20061  ->
                           match uu____20061 with
                           | (uu____20069,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____20078 -> true)))
                    in
                 if (FStar_List.length bs1) <= index
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index  in
                    FStar_Syntax_Util.mk_field_projector_name datacon
                      (FStar_Pervasives_Native.fst b) index)
             | uu____20112 -> err Prims.int_zero)
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub  ->
      let uu____20125 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub.FStar_Syntax_Syntax.target)
         in
      if uu____20125
      then
        let uu____20128 =
          let uu____20141 =
            FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub.FStar_Syntax_Syntax.target uu____20141
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____20128;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____20176 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____20176 with
           | (uu____20185,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____20204 =
                 let uu____20205 =
                   let uu___2444_20206 = ct  in
                   let uu____20207 =
                     let uu____20218 =
                       let uu____20227 =
                         let uu____20228 =
                           let uu____20235 =
                             let uu____20236 =
                               let uu____20253 =
                                 let uu____20264 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____20264; wp]  in
                               (lift_t, uu____20253)  in
                             FStar_Syntax_Syntax.Tm_app uu____20236  in
                           FStar_Syntax_Syntax.mk uu____20235  in
                         uu____20228 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____20227
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____20218]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2444_20206.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2444_20206.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____20207;
                     FStar_Syntax_Syntax.flags =
                       (uu___2444_20206.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____20205  in
               (uu____20204, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____20364 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____20364 with
           | (uu____20371,lift_t) ->
               let uu____20373 =
                 let uu____20380 =
                   let uu____20381 =
                     let uu____20398 =
                       let uu____20409 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____20418 =
                         let uu____20429 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____20438 =
                           let uu____20449 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____20449]  in
                         uu____20429 :: uu____20438  in
                       uu____20409 :: uu____20418  in
                     (lift_t, uu____20398)  in
                   FStar_Syntax_Syntax.Tm_app uu____20381  in
                 FStar_Syntax_Syntax.mk uu____20380  in
               uu____20373 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____20502 =
           let uu____20515 =
             FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____20515 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____20502;
           FStar_TypeChecker_Env.mlift_term =
             (match sub.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____20551  ->
                        fun uu____20552  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun sub  ->
      let uu____20575 = get_mlift_for_subeff env sub  in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub.FStar_Syntax_Syntax.source sub.FStar_Syntax_Syntax.target
        uu____20575
  
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
  