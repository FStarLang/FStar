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
                                                              "imspossible: mk_indexed_bind"
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
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None  ->
                       let uu____5425 = lift_comps env c1 c2 b Lift_for_bind
                          in
                       (match uu____5425 with
                        | (m,c11,c21,g_lift) ->
                            let uu____5442 =
                              let uu____5447 =
                                FStar_Syntax_Util.comp_to_comp_typ c11  in
                              let uu____5448 =
                                FStar_Syntax_Util.comp_to_comp_typ c21  in
                              (uu____5447, uu____5448)  in
                            (match uu____5442 with
                             | (ct11,ct21) ->
                                 let uu____5455 =
                                   let uu____5460 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m
                                      in
                                   if uu____5460
                                   then
                                     let bind_t =
                                       let uu____5468 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env)
                                          in
                                       FStar_All.pipe_right uu____5468
                                         FStar_Syntax_Util.get_bind_vc_combinator
                                        in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu____5471 =
                                        mk_wp_bind env m ct11 b ct21 flags r1
                                         in
                                      (uu____5471,
                                        FStar_TypeChecker_Env.trivial_guard))
                                    in
                                 (match uu____5455 with
                                  | (c,g_bind) ->
                                      let uu____5478 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind
                                         in
                                      (c, uu____5478)))))
  
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
            let uu____5514 =
              let uu____5515 =
                let uu____5526 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____5526]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____5515;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____5514  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____5571 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_5577  ->
              match uu___1_5577 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5580 -> false))
       in
    if uu____5571
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_5592  ->
              match uu___2_5592 with
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
        let uu____5620 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5620
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____5631 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____5631  in
           let pure_assume_wp1 =
             let uu____5636 = FStar_TypeChecker_Env.get_range env  in
             let uu____5637 =
               let uu____5642 =
                 let uu____5643 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____5643]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____5642  in
             uu____5637 FStar_Pervasives_Native.None uu____5636  in
           let uu____5676 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____5676)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5704 =
          let uu____5705 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5705 with
          | (c,g_c) ->
              let uu____5716 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5716
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5730 = weaken_comp env c f1  in
                     (match uu____5730 with
                      | (c1,g_w) ->
                          let uu____5741 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____5741)))
           in
        let uu____5742 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5742 weaken
  
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
                 let uu____5799 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____5799  in
               let pure_assert_wp1 =
                 let uu____5804 =
                   let uu____5809 =
                     let uu____5810 =
                       let uu____5819 = label_opt env reason r f  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                         uu____5819
                        in
                     [uu____5810]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____5809
                    in
                 uu____5804 FStar_Pervasives_Native.None r  in
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
            let uu____5889 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____5889
            then (lc, g0)
            else
              (let flags =
                 let uu____5901 =
                   let uu____5909 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____5909
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5901 with
                 | (maybe_trivial_post,flags) ->
                     let uu____5939 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_5947  ->
                               match uu___3_5947 with
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
                               | uu____5950 -> []))
                        in
                     FStar_List.append flags uu____5939
                  in
               let strengthen uu____5960 =
                 let uu____5961 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____5961 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____5980 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____5980 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____5987 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____5987
                              then
                                let uu____5991 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____5993 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____5991 uu____5993
                              else ());
                             (let uu____5998 =
                                strengthen_comp env reason c f flags  in
                              match uu____5998 with
                              | (c1,g_s) ->
                                  let uu____6009 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____6009))))
                  in
               let uu____6010 =
                 let uu____6011 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____6011
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____6010,
                 (let uu___693_6013 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___693_6013.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___693_6013.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___693_6013.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_6022  ->
            match uu___4_6022 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____6026 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____6055 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____6055
          then e
          else
            (let uu____6062 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____6065 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____6065)
                in
             if uu____6062
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
                | uu____6135 -> false  in
              if is_unit
              then
                let uu____6142 =
                  let uu____6144 =
                    let uu____6145 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____6145
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____6144
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____6142
                 then
                   let uu____6154 = FStar_Syntax_Subst.open_term_bv b phi  in
                   match uu____6154 with
                   | (b1,phi1) ->
                       let phi2 =
                         FStar_Syntax_Subst.subst
                           [FStar_Syntax_Syntax.NT
                              (b1, FStar_Syntax_Syntax.unit_const)] phi1
                          in
                       weaken_comp env c phi2
                 else
                   (let uu____6170 = close_wp_comp env [x] c  in
                    (uu____6170, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____6173 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
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
          fun uu____6201  ->
            match uu____6201 with
            | (b,lc2) ->
                let debug f =
                  let uu____6221 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____6221 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____6234 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____6234
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____6244 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____6244
                       then
                         let uu____6249 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____6249
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____6256 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____6256
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____6265 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____6265
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____6272 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____6272
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____6288 =
                  let uu____6289 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____6289
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____6297 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____6297, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____6300 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____6300 with
                     | (c1,g_c1) ->
                         let uu____6311 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____6311 with
                          | (c2,g_c2) ->
                              let trivial_guard =
                                let uu____6323 =
                                  match b with
                                  | FStar_Pervasives_Native.Some x ->
                                      let b1 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      let uu____6326 =
                                        FStar_Syntax_Syntax.is_null_binder b1
                                         in
                                      if uu____6326
                                      then g_c2
                                      else
                                        FStar_TypeChecker_Env.close_guard env
                                          [b1] g_c2
                                  | FStar_Pervasives_Native.None  -> g_c2  in
                                FStar_TypeChecker_Env.conj_guard g_c1
                                  uu____6323
                                 in
                              (debug
                                 (fun uu____6352  ->
                                    let uu____6353 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____6355 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____6360 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____6353 uu____6355 uu____6360);
                               (let aux uu____6378 =
                                  let uu____6379 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____6379
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____6410
                                        ->
                                        let uu____6411 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____6411
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____6443 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____6443
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____6490 =
                                  let aux_with_trivial_guard uu____6520 =
                                    let uu____6521 = aux ()  in
                                    match uu____6521 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c, trivial_guard, reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____6579 =
                                    let uu____6581 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____6581  in
                                  if uu____6579
                                  then
                                    let uu____6597 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____6597
                                     then
                                       FStar_Util.Inl
                                         (c2, trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____6624 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____6624))
                                  else
                                    (let uu____6641 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____6641
                                     then
                                       let close_with_type_of_x x c =
                                         let x1 =
                                           let uu___796_6672 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___796_6672.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___796_6672.FStar_Syntax_Syntax.index);
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
                                           let uu____6703 =
                                             let uu____6708 =
                                               FStar_All.pipe_right c2
                                                 (FStar_Syntax_Subst.subst_comp
                                                    [FStar_Syntax_Syntax.NT
                                                       (x, e)])
                                                in
                                             FStar_All.pipe_right uu____6708
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6703 with
                                            | (c21,g_close) ->
                                                let uu____6729 =
                                                  let uu____6737 =
                                                    let uu____6738 =
                                                      let uu____6741 =
                                                        let uu____6744 =
                                                          FStar_TypeChecker_Env.map_guard
                                                            g_c2
                                                            (FStar_Syntax_Subst.subst
                                                               [FStar_Syntax_Syntax.NT
                                                                  (x, e)])
                                                           in
                                                        [uu____6744; g_close]
                                                         in
                                                      g_c1 :: uu____6741  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6738
                                                     in
                                                  (c21, uu____6737, "c1 Tot")
                                                   in
                                                FStar_Util.Inl uu____6729)
                                       | (uu____6757,FStar_Pervasives_Native.Some
                                          x) ->
                                           let uu____6769 =
                                             FStar_All.pipe_right c2
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6769 with
                                            | (c21,g_close) ->
                                                let uu____6792 =
                                                  let uu____6800 =
                                                    let uu____6801 =
                                                      let uu____6804 =
                                                        let uu____6807 =
                                                          let uu____6808 =
                                                            let uu____6809 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____6809]  in
                                                          FStar_TypeChecker_Env.close_guard
                                                            env uu____6808
                                                            g_c2
                                                           in
                                                        [uu____6807; g_close]
                                                         in
                                                      g_c1 :: uu____6804  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6801
                                                     in
                                                  (c21, uu____6800,
                                                    "c1 Tot only close")
                                                   in
                                                FStar_Util.Inl uu____6792)
                                       | (uu____6838,uu____6839) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____6854 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____6854
                                        then
                                          let uu____6869 =
                                            let uu____6877 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____6877, trivial_guard,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____6869
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____6890 = try_simplify ()  in
                                match uu____6890 with
                                | FStar_Util.Inl (c,g,reason) ->
                                    (debug
                                       (fun uu____6925  ->
                                          let uu____6926 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____6926);
                                     (c, g))
                                | FStar_Util.Inr reason ->
                                    (debug
                                       (fun uu____6942  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 g =
                                        let uu____6973 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____6973 with
                                        | (c,g_bind) ->
                                            let uu____6984 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g g_bind
                                               in
                                            (c, uu____6984)
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
                                        let uu____7011 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____7011 with
                                        | (m,uu____7023,lift2) ->
                                            let uu____7025 =
                                              lift_comp env c22 lift2  in
                                            (match uu____7025 with
                                             | (c23,g2) ->
                                                 let uu____7036 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____7036 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let trivial =
                                                        let uu____7052 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7052
                                                          FStar_Util.must
                                                         in
                                                      let vc1 =
                                                        let uu____7062 =
                                                          let uu____7067 =
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              trivial
                                                             in
                                                          let uu____7068 =
                                                            let uu____7069 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____7078 =
                                                              let uu____7089
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____7089]
                                                               in
                                                            uu____7069 ::
                                                              uu____7078
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7067
                                                            uu____7068
                                                           in
                                                        uu____7062
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____7122 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____7122 with
                                                       | (c,g_s) ->
                                                           let uu____7137 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____7137))))
                                         in
                                      let uu____7138 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____7154 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____7154, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____7138 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____7170 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____7170
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____7179 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____7179
                                             then
                                               (debug
                                                  (fun uu____7193  ->
                                                     let uu____7194 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____7196 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____7194 uu____7196);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 let g =
                                                   let uu____7203 =
                                                     FStar_TypeChecker_Env.map_guard
                                                       g_c2
                                                       (FStar_Syntax_Subst.subst
                                                          [FStar_Syntax_Syntax.NT
                                                             (x, e1)])
                                                      in
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 uu____7203
                                                    in
                                                 mk_bind1 c1 b c21 g))
                                             else
                                               (let uu____7208 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____7211 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____7211)
                                                   in
                                                if uu____7208
                                                then
                                                  let e1' =
                                                    let uu____7236 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____7236
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug
                                                     (fun uu____7248  ->
                                                        let uu____7249 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____7251 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____7249
                                                          uu____7251);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug
                                                     (fun uu____7266  ->
                                                        let uu____7267 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____7269 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____7267
                                                          uu____7269);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____7276 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____7276
                                                       in
                                                    let uu____7277 =
                                                      let uu____7282 =
                                                        let uu____7283 =
                                                          let uu____7284 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____7284]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____7283
                                                         in
                                                      weaken_comp uu____7282
                                                        c21 x_eq_e
                                                       in
                                                    match uu____7277 with
                                                    | (c22,g_w) ->
                                                        let g =
                                                          let uu____7310 =
                                                            let uu____7311 =
                                                              let uu____7312
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x
                                                                 in
                                                              [uu____7312]
                                                               in
                                                            let uu____7331 =
                                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                                g_c2 x_eq_e
                                                               in
                                                            FStar_TypeChecker_Env.close_guard
                                                              env uu____7311
                                                              uu____7331
                                                             in
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g_c1 uu____7310
                                                           in
                                                        let uu____7332 =
                                                          mk_bind1 c1 b c22 g
                                                           in
                                                        (match uu____7332
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____7343 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____7343))))))
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
      | uu____7360 -> g2
  
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
            (let uu____7384 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____7384)
           in
        let flags =
          if should_return1
          then
            let uu____7392 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____7392
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine uu____7410 =
          let uu____7411 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____7411 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____7424 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____7424
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____7432 =
                  let uu____7434 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____7434  in
                (if uu____7432
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___921_7443 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___921_7443.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___921_7443.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___921_7443.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____7444 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____7444, g_c)
                 else
                   (let uu____7447 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____7447, g_c)))
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
                   let uu____7458 =
                     let uu____7459 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____7459
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____7458
                    in
                 let eq = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret
                     (FStar_TypeChecker_Common.NonTrivial eq)
                    in
                 let uu____7462 =
                   let uu____7467 =
                     let uu____7468 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____7468
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____7467  in
                 match uu____7462 with
                 | (bind_c,g_bind) ->
                     let uu____7477 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____7478 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____7477, uu____7478))
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
            fun uu____7514  ->
              match uu____7514 with
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
                    let uu____7526 =
                      ((let uu____7530 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____7530) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____7526
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____7548 =
        let uu____7549 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____7549  in
      FStar_Syntax_Syntax.fvar uu____7548 FStar_Syntax_Syntax.delta_constant
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
                  let uu____7599 =
                    let uu____7604 =
                      let uu____7605 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____7605 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7604 [u_a]
                     in
                  match uu____7599 with
                  | (uu____7616,conjunction) ->
                      let uu____7618 =
                        let uu____7627 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____7642 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____7627, uu____7642)  in
                      (match uu____7618 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____7688 =
                               let uu____7690 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____7690 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7688)
                              in
                           let uu____7694 =
                             let uu____7739 =
                               let uu____7740 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____7740.FStar_Syntax_Syntax.n  in
                             match uu____7739 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____7789) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____7821 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____7821 with
                                  | (a_b::bs1,body1) ->
                                      let uu____7893 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____7893 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____8041 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____8041)))
                             | uu____8074 ->
                                 let uu____8075 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____8075 r
                              in
                           (match uu____7694 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____8200 =
                                  let uu____8207 =
                                    let uu____8208 =
                                      let uu____8209 =
                                        let uu____8216 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____8216, a)  in
                                      FStar_Syntax_Syntax.NT uu____8209  in
                                    [uu____8208]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____8207
                                    (fun b  ->
                                       let uu____8232 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____8234 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____8236 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____8232 uu____8234 uu____8236) r
                                   in
                                (match uu____8200 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____8274 =
                                                let uu____8281 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____8281, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____8274) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____8320 =
                                           let uu____8321 =
                                             let uu____8324 =
                                               let uu____8325 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8325.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8324
                                              in
                                           uu____8321.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8320 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8336,uu____8337::is) ->
                                             let uu____8379 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8379
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8412 ->
                                             let uu____8413 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8413 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____8429 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8429)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____8434 =
                                           let uu____8435 =
                                             let uu____8438 =
                                               let uu____8439 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8439.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8438
                                              in
                                           uu____8435.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8434 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8450,uu____8451::is) ->
                                             let uu____8493 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8493
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8526 ->
                                             let uu____8527 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8527 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____8543 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8543)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____8548 =
                                         let uu____8549 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____8549.FStar_Syntax_Syntax.n  in
                                       match uu____8548 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8554,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8609 ->
                                           let uu____8610 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____8610 r
                                        in
                                     let uu____8619 =
                                       let uu____8620 =
                                         let uu____8621 =
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
                                             uu____8621;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____8620
                                        in
                                     let uu____8644 =
                                       let uu____8645 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8645 g_guard
                                        in
                                     (uu____8619, uu____8644))))
  
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
                fun uu____8690  ->
                  let if_then_else =
                    let uu____8696 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____8696 FStar_Util.must  in
                  let uu____8703 = destruct_wp_comp ct1  in
                  match uu____8703 with
                  | (uu____8714,uu____8715,wp_t) ->
                      let uu____8717 = destruct_wp_comp ct2  in
                      (match uu____8717 with
                       | (uu____8728,uu____8729,wp_e) ->
                           let wp =
                             let uu____8734 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             let uu____8735 =
                               let uu____8740 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_a] env ed if_then_else
                                  in
                               let uu____8741 =
                                 let uu____8742 =
                                   FStar_Syntax_Syntax.as_arg a  in
                                 let uu____8751 =
                                   let uu____8762 =
                                     FStar_Syntax_Syntax.as_arg p  in
                                   let uu____8771 =
                                     let uu____8782 =
                                       FStar_Syntax_Syntax.as_arg wp_t  in
                                     let uu____8791 =
                                       let uu____8802 =
                                         FStar_Syntax_Syntax.as_arg wp_e  in
                                       [uu____8802]  in
                                     uu____8782 :: uu____8791  in
                                   uu____8762 :: uu____8771  in
                                 uu____8742 :: uu____8751  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____8740
                                 uu____8741
                                in
                             uu____8735 FStar_Pervasives_Native.None
                               uu____8734
                              in
                           let uu____8851 = mk_comp ed u_a a wp []  in
                           (uu____8851, FStar_TypeChecker_Env.trivial_guard))
  
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
            let uu____8905 =
              let uu____8906 =
                FStar_All.pipe_right scrutinee FStar_Syntax_Syntax.mk_binder
                 in
              [uu____8906]  in
            FStar_TypeChecker_Env.push_binders env0 uu____8905  in
          let eff =
            FStar_List.fold_left
              (fun eff  ->
                 fun uu____8953  ->
                   match uu____8953 with
                   | (uu____8967,eff_label,uu____8969,uu____8970) ->
                       join_effects env eff eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases
             in
          let uu____8983 =
            let uu____8991 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu____9029  ->
                      match uu____9029 with
                      | (uu____9044,uu____9045,flags,uu____9047) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___5_9064  ->
                                  match uu___5_9064 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                      true
                                  | uu____9067 -> false))))
               in
            if uu____8991
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, [])  in
          match uu____8983 with
          | (should_not_inline_whole_match,bind_cases_flags) ->
              let bind_cases uu____9104 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                   in
                let uu____9106 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                   in
                if uu____9106
                then
                  let uu____9113 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                     in
                  (uu____9113, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let default_case =
                     let post_k =
                       let uu____9120 =
                         let uu____9129 =
                           FStar_Syntax_Syntax.null_binder res_t  in
                         [uu____9129]  in
                       let uu____9148 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9120 uu____9148  in
                     let kwp =
                       let uu____9154 =
                         let uu____9163 =
                           FStar_Syntax_Syntax.null_binder post_k  in
                         [uu____9163]  in
                       let uu____9182 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9154 uu____9182  in
                     let post =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None post_k
                        in
                     let wp =
                       let uu____9189 =
                         let uu____9190 = FStar_Syntax_Syntax.mk_binder post
                            in
                         [uu____9190]  in
                       let uu____9209 =
                         let uu____9212 =
                           let uu____9219 =
                             FStar_TypeChecker_Env.get_range env  in
                           label FStar_TypeChecker_Err.exhaustiveness_check
                             uu____9219
                            in
                         let uu____9220 =
                           fvar_const env FStar_Parser_Const.false_lid  in
                         FStar_All.pipe_left uu____9212 uu____9220  in
                       FStar_Syntax_Util.abs uu____9189 uu____9209
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
                     let uu____9244 =
                       should_not_inline_whole_match ||
                         (let uu____9247 = is_pure_or_ghost_effect env eff
                             in
                          Prims.op_Negation uu____9247)
                        in
                     if uu____9244 then cthen true else cthen false  in
                   let branch_conditions =
                     let uu____9259 =
                       let uu____9272 =
                         let uu____9277 =
                           let uu____9288 =
                             FStar_All.pipe_right lcases
                               (FStar_List.map
                                  (fun uu____9332  ->
                                     match uu____9332 with
                                     | (g,uu____9347,uu____9348,uu____9349)
                                         -> g))
                              in
                           FStar_All.pipe_right uu____9288
                             (FStar_List.fold_left
                                (fun uu____9393  ->
                                   fun g  ->
                                     match uu____9393 with
                                     | (conds,acc) ->
                                         let cond =
                                           let uu____9434 =
                                             FStar_Syntax_Util.mk_neg g  in
                                           FStar_Syntax_Util.mk_conj acc
                                             uu____9434
                                            in
                                         ((FStar_List.append conds [cond]),
                                           cond))
                                ([FStar_Syntax_Util.t_true],
                                  FStar_Syntax_Util.t_true))
                            in
                         FStar_All.pipe_right uu____9277
                           FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____9272
                         (FStar_List.splitAt (FStar_List.length lcases))
                        in
                     FStar_All.pipe_right uu____9259
                       FStar_Pervasives_Native.fst
                      in
                   let uu____9535 =
                     FStar_List.fold_right2
                       (fun uu____9598  ->
                          fun bcond  ->
                            fun uu____9600  ->
                              match (uu____9598, uu____9600) with
                              | ((g,eff_label,uu____9660,cthen),(uu____9662,celse,g_comp))
                                  ->
                                  let uu____9709 =
                                    let uu____9714 =
                                      maybe_return eff_label cthen  in
                                    FStar_TypeChecker_Common.lcomp_comp
                                      uu____9714
                                     in
                                  (match uu____9709 with
                                   | (cthen1,gthen) ->
                                       let gthen1 =
                                         let uu____9726 =
                                           FStar_Syntax_Util.mk_conj bcond g
                                            in
                                         FStar_TypeChecker_Common.weaken_guard_formula
                                           gthen uu____9726
                                          in
                                       let uu____9727 =
                                         let uu____9738 =
                                           lift_comps_sep_guards env cthen1
                                             celse
                                             FStar_Pervasives_Native.None
                                             Lift_for_match
                                            in
                                         match uu____9738 with
                                         | (m,cthen2,celse1,g_lift_then,g_lift_else)
                                             ->
                                             let md =
                                               FStar_TypeChecker_Env.get_effect_decl
                                                 env m
                                                in
                                             let uu____9765 =
                                               FStar_All.pipe_right cthen2
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                in
                                             let uu____9766 =
                                               FStar_All.pipe_right celse1
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                in
                                             (md, uu____9765, uu____9766,
                                               g_lift_then, g_lift_else)
                                          in
                                       (match uu____9727 with
                                        | (md,ct_then,ct_else,g_lift_then,g_lift_else)
                                            ->
                                            let fn =
                                              let uu____9817 =
                                                FStar_All.pipe_right md
                                                  FStar_Syntax_Util.is_layered
                                                 in
                                              if uu____9817
                                              then mk_layered_conjunction
                                              else mk_non_layered_conjunction
                                               in
                                            let g_lift_then1 =
                                              let uu____9852 =
                                                FStar_Syntax_Util.mk_conj
                                                  bcond g
                                                 in
                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                g_lift_then uu____9852
                                               in
                                            let g_lift_else1 =
                                              let uu____9854 =
                                                let uu____9855 =
                                                  FStar_Syntax_Util.mk_neg g
                                                   in
                                                FStar_Syntax_Util.mk_conj
                                                  bcond uu____9855
                                                 in
                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                g_lift_else uu____9854
                                               in
                                            let g_lift =
                                              FStar_TypeChecker_Env.conj_guard
                                                g_lift_then1 g_lift_else1
                                               in
                                            let uu____9859 =
                                              let uu____9864 =
                                                FStar_TypeChecker_Env.get_range
                                                  env
                                                 in
                                              fn env md u_res_t res_t g
                                                ct_then ct_else uu____9864
                                               in
                                            (match uu____9859 with
                                             | (c,g_conjunction) ->
                                                 let uu____9875 =
                                                   FStar_TypeChecker_Env.conj_guards
                                                     [g_comp;
                                                     gthen1;
                                                     g_lift;
                                                     g_conjunction]
                                                    in
                                                 ((FStar_Pervasives_Native.Some
                                                     md), c, uu____9875)))))
                       lcases branch_conditions
                       (FStar_Pervasives_Native.None, default_case,
                         FStar_TypeChecker_Env.trivial_guard)
                      in
                   match uu____9535 with
                   | (md,comp,g_comp) ->
                       let g_comp1 =
                         let uu____9892 =
                           let uu____9893 =
                             FStar_All.pipe_right scrutinee
                               FStar_Syntax_Syntax.mk_binder
                              in
                           [uu____9893]  in
                         FStar_TypeChecker_Env.close_guard env0 uu____9892
                           g_comp
                          in
                       (match lcases with
                        | [] -> (comp, g_comp1)
                        | uu____9936::[] -> (comp, g_comp1)
                        | uu____9979 ->
                            let uu____9996 =
                              let uu____9998 =
                                FStar_All.pipe_right md FStar_Util.must  in
                              FStar_All.pipe_right uu____9998
                                FStar_Syntax_Util.is_layered
                               in
                            if uu____9996
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
                               let uu____10011 = destruct_wp_comp comp1  in
                               match uu____10011 with
                               | (uu____10022,uu____10023,wp) ->
                                   let ite_wp =
                                     let uu____10026 =
                                       FStar_All.pipe_right md1
                                         FStar_Syntax_Util.get_wp_ite_combinator
                                        in
                                     FStar_All.pipe_right uu____10026
                                       FStar_Util.must
                                      in
                                   let wp1 =
                                     let uu____10036 =
                                       let uu____10041 =
                                         FStar_TypeChecker_Env.inst_effect_fun_with
                                           [u_res_t] env md1 ite_wp
                                          in
                                       let uu____10042 =
                                         let uu____10043 =
                                           FStar_Syntax_Syntax.as_arg res_t
                                            in
                                         let uu____10052 =
                                           let uu____10063 =
                                             FStar_Syntax_Syntax.as_arg wp
                                              in
                                           [uu____10063]  in
                                         uu____10043 :: uu____10052  in
                                       FStar_Syntax_Syntax.mk_Tm_app
                                         uu____10041 uu____10042
                                        in
                                     uu____10036 FStar_Pervasives_Native.None
                                       wp.FStar_Syntax_Syntax.pos
                                      in
                                   let uu____10096 =
                                     mk_comp md1 u_res_t res_t wp1
                                       bind_cases_flags
                                      in
                                   (uu____10096, g_comp1))))
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
          let uu____10131 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____10131 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____10147 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____10153 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____10147 uu____10153
              else
                (let uu____10162 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____10168 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____10162 uu____10168)
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
          let uu____10193 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____10193
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____10196 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____10196
        then u_res
        else
          (let is_total =
             let uu____10203 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____10203
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____10214 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____10214 with
              | FStar_Pervasives_Native.None  ->
                  let uu____10217 =
                    let uu____10223 =
                      let uu____10225 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____10225
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____10223)
                     in
                  FStar_Errors.raise_error uu____10217
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
      let uu____10249 = destruct_wp_comp ct  in
      match uu____10249 with
      | (u_t,t,wp) ->
          let vc =
            let uu____10268 = FStar_TypeChecker_Env.get_range env  in
            let uu____10269 =
              let uu____10274 =
                let uu____10275 =
                  let uu____10276 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_trivial_combinator
                     in
                  FStar_All.pipe_right uu____10276 FStar_Util.must  in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____10275
                 in
              let uu____10283 =
                let uu____10284 = FStar_Syntax_Syntax.as_arg t  in
                let uu____10293 =
                  let uu____10304 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____10304]  in
                uu____10284 :: uu____10293  in
              FStar_Syntax_Syntax.mk_Tm_app uu____10274 uu____10283  in
            uu____10269 FStar_Pervasives_Native.None uu____10268  in
          let uu____10337 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____10337)
  
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
                  let uu____10392 =
                    FStar_TypeChecker_Env.try_lookup_lid env f  in
                  match uu____10392 with
                  | FStar_Pervasives_Native.Some uu____10407 ->
                      ((let uu____10425 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____10425
                        then
                          let uu____10429 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____10429
                        else ());
                       (let coercion =
                          let uu____10435 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____10435
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____10442 =
                            let uu____10443 =
                              let uu____10444 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10444
                               in
                            (FStar_Pervasives_Native.None, uu____10443)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____10442
                           in
                        let e1 =
                          let uu____10450 =
                            let uu____10455 =
                              let uu____10456 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____10456]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____10455
                             in
                          uu____10450 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____10490 =
                          let uu____10496 =
                            let uu____10498 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____10498
                             in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____10496)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____10490);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____10517 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10535 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10546 -> false 
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
      let uu____10570 = FStar_Syntax_Util.head_and_args t2  in
      match uu____10570 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____10615 =
              let uu____10630 =
                let uu____10631 = FStar_Syntax_Subst.compress h1  in
                uu____10631.FStar_Syntax_Syntax.n  in
              (uu____10630, args)  in
            match uu____10615 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____10678,uu____10679) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____10712) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match
               (uu____10733,branches),uu____10735) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc  ->
                        fun br  ->
                          match acc with
                          | Yes uu____10799 -> Maybe
                          | Maybe  -> Maybe
                          | No  ->
                              let uu____10800 =
                                FStar_Syntax_Subst.open_branch br  in
                              (match uu____10800 with
                               | (uu____10801,uu____10802,br_body) ->
                                   let uu____10820 =
                                     let uu____10821 =
                                       let uu____10826 =
                                         let uu____10827 =
                                           let uu____10830 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names
                                              in
                                           FStar_All.pipe_right uu____10830
                                             FStar_Util.set_elements
                                            in
                                         FStar_All.pipe_right uu____10827
                                           (FStar_TypeChecker_Env.push_bvs
                                              env)
                                          in
                                       check_erased uu____10826  in
                                     FStar_All.pipe_right br_body uu____10821
                                      in
                                   (match uu____10820 with
                                    | No  -> No
                                    | uu____10841 -> Maybe))) No)
            | uu____10842 -> No  in
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
            (((let uu____10894 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____10894) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____10913 =
                 let uu____10914 = FStar_Syntax_Subst.compress t1  in
                 uu____10914.FStar_Syntax_Syntax.n  in
               match uu____10913 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____10919 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____10929 =
                 let uu____10930 = FStar_Syntax_Subst.compress t1  in
                 uu____10930.FStar_Syntax_Syntax.n  in
               match uu____10929 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____10935 -> false  in
             let is_type t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let t2 = FStar_Syntax_Util.unrefine t1  in
               let uu____10946 =
                 let uu____10947 = FStar_Syntax_Subst.compress t2  in
                 uu____10947.FStar_Syntax_Syntax.n  in
               match uu____10946 with
               | FStar_Syntax_Syntax.Tm_type uu____10951 -> true
               | uu____10953 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____10956 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____10956 with
             | (head,args) ->
                 ((let uu____11006 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____11006
                   then
                     let uu____11010 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____11012 = FStar_Syntax_Print.term_to_string e
                        in
                     let uu____11014 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____11016 =
                       FStar_Syntax_Print.term_to_string exp_t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____11010 uu____11012 uu____11014 uu____11016
                   else ());
                  (let mk_erased u t =
                     let uu____11034 =
                       let uu____11037 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____11037 [u]  in
                     let uu____11038 =
                       let uu____11049 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____11049]  in
                     FStar_Syntax_Util.mk_app uu____11034 uu____11038  in
                   let uu____11074 =
                     let uu____11089 =
                       let uu____11090 = FStar_Syntax_Util.un_uinst head  in
                       uu____11090.FStar_Syntax_Syntax.n  in
                     (uu____11089, args)  in
                   match uu____11074 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type exp_t)
                       ->
                       let uu____11128 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____11128 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____11168 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11168 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11208 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11208 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11248 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11248 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____11269 ->
                       let uu____11284 =
                         let uu____11289 = check_erased env res_typ  in
                         let uu____11290 = check_erased env exp_t  in
                         (uu____11289, uu____11290)  in
                       (match uu____11284 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11299 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____11299 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____11310 =
                                   let uu____11315 =
                                     let uu____11316 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____11316]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____11315
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____11310 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11351 =
                              let uu____11356 =
                                let uu____11357 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____11357]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____11356
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____11351 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____11390 ->
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
        let uu____11425 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____11425 with
        | (hd,args) ->
            let uu____11474 =
              let uu____11489 =
                let uu____11490 = FStar_Syntax_Subst.compress hd  in
                uu____11490.FStar_Syntax_Syntax.n  in
              (uu____11489, args)  in
            (match uu____11474 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____11528 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun uu____11555  ->
                      FStar_Pervasives_Native.Some uu____11555) uu____11528
             | uu____11556 -> FStar_Pervasives_Native.None)
  
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
          (let uu____11609 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____11609
           then
             let uu____11612 = FStar_Syntax_Print.term_to_string e  in
             let uu____11614 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____11616 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____11612 uu____11614 uu____11616
           else ());
          (let use_eq =
             (env.FStar_TypeChecker_Env.use_eq_strict ||
                env.FStar_TypeChecker_Env.use_eq)
               ||
               (let uu____11626 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____11626 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____11651 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____11677 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____11677, false)
             else
               (let uu____11687 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____11687, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____11700) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____11712 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____11712
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1363_11728 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1363_11728.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1363_11728.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1363_11728.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard) ->
               let uu____11735 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____11735 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____11751 =
                      let uu____11752 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____11752 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____11772 =
                            let uu____11774 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____11774 = FStar_Syntax_Util.Equal  in
                          if uu____11772
                          then
                            ((let uu____11781 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____11781
                              then
                                let uu____11785 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____11787 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____11785 uu____11787
                              else ());
                             (let uu____11792 = set_result_typ c  in
                              (uu____11792, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____11799 ->
                                   true
                               | uu____11807 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____11816 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____11816
                                  in
                               let lc1 =
                                 let uu____11818 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____11819 =
                                   let uu____11820 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____11820)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____11818 uu____11819
                                  in
                               ((let uu____11824 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____11824
                                 then
                                   let uu____11828 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____11830 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____11832 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____11834 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____11828 uu____11830 uu____11832
                                     uu____11834
                                 else ());
                                (let uu____11839 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____11839 with
                                 | (c1,g_lc) ->
                                     let uu____11850 = set_result_typ c1  in
                                     let uu____11851 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____11850, uu____11851)))
                             else
                               ((let uu____11855 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____11855
                                 then
                                   let uu____11859 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____11861 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____11859 uu____11861
                                 else ());
                                (let uu____11866 = set_result_typ c  in
                                 (uu____11866, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1400_11870 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1400_11870.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1400_11870.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1400_11870.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____11880 =
                      let uu____11881 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____11881
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____11891 =
                           let uu____11892 = FStar_Syntax_Subst.compress f1
                              in
                           uu____11892.FStar_Syntax_Syntax.n  in
                         match uu____11891 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____11899,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____11901;
                                            FStar_Syntax_Syntax.vars =
                                              uu____11902;_},uu____11903)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1416_11929 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1416_11929.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1416_11929.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1416_11929.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____11930 ->
                             let uu____11931 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____11931 with
                              | (c,g_c) ->
                                  ((let uu____11943 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____11943
                                    then
                                      let uu____11947 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____11949 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____11951 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____11953 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____11947 uu____11949 uu____11951
                                        uu____11953
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
                                        let uu____11966 =
                                          let uu____11971 =
                                            let uu____11972 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____11972]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____11971
                                           in
                                        uu____11966
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____11999 =
                                      let uu____12004 =
                                        FStar_All.pipe_left
                                          (fun uu____12025  ->
                                             FStar_Pervasives_Native.Some
                                               uu____12025)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____12026 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____12027 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____12028 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____12004
                                        uu____12026 e uu____12027 uu____12028
                                       in
                                    match uu____11999 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1434_12036 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1434_12036.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1434_12036.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____12038 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____12038
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____12041 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____12041 with
                                         | (c2,g_lc) ->
                                             ((let uu____12053 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____12053
                                               then
                                                 let uu____12057 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____12057
                                               else ());
                                              (let uu____12062 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____12062))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_12071  ->
                              match uu___6_12071 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____12074 -> []))
                       in
                    let lc1 =
                      let uu____12076 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____12076 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1450_12078 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1450_12078.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1450_12078.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1450_12078.FStar_TypeChecker_Common.implicits)
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
        let uu____12114 =
          let uu____12117 =
            let uu____12122 =
              let uu____12123 =
                let uu____12132 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____12132  in
              [uu____12123]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____12122  in
          uu____12117 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____12114  in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____12155 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____12155
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____12174 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____12190 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____12207 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____12207
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____12223)::(ens,uu____12225)::uu____12226 ->
                    let uu____12269 =
                      let uu____12272 = norm req  in
                      FStar_Pervasives_Native.Some uu____12272  in
                    let uu____12273 =
                      let uu____12274 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm uu____12274  in
                    (uu____12269, uu____12273)
                | uu____12277 ->
                    let uu____12288 =
                      let uu____12294 =
                        let uu____12296 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____12296
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____12294)
                       in
                    FStar_Errors.raise_error uu____12288
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____12316)::uu____12317 ->
                    let uu____12344 =
                      let uu____12349 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____12349
                       in
                    (match uu____12344 with
                     | (us_r,uu____12381) ->
                         let uu____12382 =
                           let uu____12387 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____12387
                            in
                         (match uu____12382 with
                          | (us_e,uu____12419) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____12422 =
                                  let uu____12423 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12423
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12422
                                  us_r
                                 in
                              let as_ens =
                                let uu____12425 =
                                  let uu____12426 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12426
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12425
                                  us_e
                                 in
                              let req =
                                let uu____12430 =
                                  let uu____12435 =
                                    let uu____12436 =
                                      let uu____12447 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12447]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12436
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____12435
                                   in
                                uu____12430 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____12487 =
                                  let uu____12492 =
                                    let uu____12493 =
                                      let uu____12504 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12504]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12493
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____12492
                                   in
                                uu____12487 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____12541 =
                                let uu____12544 = norm req  in
                                FStar_Pervasives_Native.Some uu____12544  in
                              let uu____12545 =
                                let uu____12546 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm uu____12546  in
                              (uu____12541, uu____12545)))
                | uu____12549 -> failwith "Impossible"))
  
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
        (let uu____12588 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____12588
         then
           let uu____12593 = FStar_Syntax_Print.term_to_string tm  in
           let uu____12595 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____12593
             uu____12595
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
          (let uu____12654 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____12654
           then
             let uu____12659 = FStar_Syntax_Print.term_to_string tm  in
             let uu____12661 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____12659
               uu____12661
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____12672 =
      let uu____12674 =
        let uu____12675 = FStar_Syntax_Subst.compress t  in
        uu____12675.FStar_Syntax_Syntax.n  in
      match uu____12674 with
      | FStar_Syntax_Syntax.Tm_app uu____12679 -> false
      | uu____12697 -> true  in
    if uu____12672
    then t
    else
      (let uu____12702 = FStar_Syntax_Util.head_and_args t  in
       match uu____12702 with
       | (head,args) ->
           let uu____12745 =
             let uu____12747 =
               let uu____12748 = FStar_Syntax_Subst.compress head  in
               uu____12748.FStar_Syntax_Syntax.n  in
             match uu____12747 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____12753 -> false  in
           if uu____12745
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____12785 ->
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
          ((let uu____12832 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____12832
            then
              let uu____12835 = FStar_Syntax_Print.term_to_string e  in
              let uu____12837 = FStar_Syntax_Print.term_to_string t  in
              let uu____12839 =
                let uu____12841 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____12841
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____12835 uu____12837 uu____12839
            else ());
           (let unfolded_arrow_formals t1 =
              let rec aux bs t2 =
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf env t2  in
                let uu____12877 = FStar_Syntax_Util.arrow_formals t3  in
                match uu____12877 with
                | (bs',t4) ->
                    (match bs' with
                     | [] -> bs
                     | bs'1 -> aux (FStar_List.append bs bs'1) t4)
                 in
              aux [] t1  in
            let number_of_implicits t1 =
              let formals = unfolded_arrow_formals t1  in
              let n_implicits =
                let uu____12911 =
                  FStar_All.pipe_right formals
                    (FStar_Util.prefix_until
                       (fun uu____12989  ->
                          match uu____12989 with
                          | (uu____12997,imp) ->
                              (FStar_Option.isNone imp) ||
                                (let uu____13004 =
                                   FStar_Syntax_Util.eq_aqual imp
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Equality)
                                    in
                                 uu____13004 = FStar_Syntax_Util.Equal)))
                   in
                match uu____12911 with
                | FStar_Pervasives_Native.None  -> FStar_List.length formals
                | FStar_Pervasives_Native.Some
                    (implicits,_first_explicit,_rest) ->
                    FStar_List.length implicits
                 in
              n_implicits  in
            let inst_n_binders t1 =
              let uu____13123 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____13123 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____13137 =
                      let uu____13143 =
                        let uu____13145 = FStar_Util.string_of_int n_expected
                           in
                        let uu____13147 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____13149 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____13145 uu____13147 uu____13149
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____13143)
                       in
                    let uu____13153 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____13137 uu____13153
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_13171 =
              match uu___7_13171 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____13214 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____13214 with
                 | (bs1,c1) ->
                     let rec aux subst inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some
                          uu____13345,uu____13332) when
                           uu____13345 = Prims.int_zero ->
                           ([], bs2, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____13378,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____13380))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____13414 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____13414 with
                            | (v,uu____13455,g) ->
                                ((let uu____13470 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13470
                                  then
                                    let uu____13473 =
                                      FStar_Syntax_Print.term_to_string v  in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____13473
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst
                                     in
                                  let uu____13483 =
                                    aux subst1 (decr_inst inst_n) rest  in
                                  match uu____13483 with
                                  | (args,bs3,subst2,g') ->
                                      let uu____13576 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____13576))))
                       | (uu____13603,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____13640 =
                             let uu____13653 =
                               let uu____13660 =
                                 let uu____13665 = FStar_Dyn.mkdyn env  in
                                 (uu____13665, tau)  in
                               FStar_Pervasives_Native.Some uu____13660  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____13653
                              in
                           (match uu____13640 with
                            | (v,uu____13698,g) ->
                                ((let uu____13713 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13713
                                  then
                                    let uu____13716 =
                                      FStar_Syntax_Print.term_to_string v  in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____13716
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst
                                     in
                                  let uu____13726 =
                                    aux subst1 (decr_inst inst_n) rest  in
                                  match uu____13726 with
                                  | (args,bs3,subst2,g') ->
                                      let uu____13819 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____13819))))
                       | (uu____13846,bs3) ->
                           ([], bs3, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____13894 =
                       let uu____13921 = inst_n_binders t1  in
                       aux [] uu____13921 bs1  in
                     (match uu____13894 with
                      | (args,bs2,subst,guard) ->
                          (match (args, bs2) with
                           | ([],uu____13993) -> (e, torig, guard)
                           | (uu____14024,[]) when
                               let uu____14055 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____14055 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____14057 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____14085 ->
                                     FStar_Syntax_Util.arrow bs2 c1
                                  in
                               let t3 = FStar_Syntax_Subst.subst subst t2  in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   FStar_Pervasives_Native.None
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               (e1, t3, guard))))
            | uu____14098 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs  ->
    let uu____14110 =
      let uu____14114 = FStar_Util.set_elements univs  in
      FStar_All.pipe_right uu____14114
        (FStar_List.map
           (fun u  ->
              let uu____14126 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____14126 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____14110 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____14154 = FStar_Util.set_is_empty x  in
      if uu____14154
      then []
      else
        (let s =
           let uu____14174 =
             let uu____14177 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____14177  in
           FStar_All.pipe_right uu____14174 FStar_Util.set_elements  in
         (let uu____14195 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____14195
          then
            let uu____14200 =
              let uu____14202 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____14202  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____14200
          else ());
         (let r =
            let uu____14211 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____14211  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____14256 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____14256
                     then
                       let uu____14261 =
                         let uu____14263 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____14263
                          in
                       let uu____14267 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____14269 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____14261 uu____14267 uu____14269
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
        let uu____14299 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____14299 FStar_Util.set_elements  in
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
        | ([],uu____14338) -> generalized_univ_names
        | (uu____14345,[]) -> explicit_univ_names
        | uu____14352 ->
            let uu____14361 =
              let uu____14367 =
                let uu____14369 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____14369
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____14367)
               in
            FStar_Errors.raise_error uu____14361 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____14391 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____14391
       then
         let uu____14396 = FStar_Syntax_Print.term_to_string t  in
         let uu____14398 = FStar_Syntax_Print.univ_names_to_string univnames
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____14396 uu____14398
       else ());
      (let univs = FStar_Syntax_Free.univs t  in
       (let uu____14407 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____14407
        then
          let uu____14412 = string_of_univs univs  in
          FStar_Util.print1 "univs to gen : %s\n" uu____14412
        else ());
       (let gen = gen_univs env univs  in
        (let uu____14421 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____14421
         then
           let uu____14426 = FStar_Syntax_Print.term_to_string t  in
           let uu____14428 = FStar_Syntax_Print.univ_names_to_string gen  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____14426 uu____14428
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
        let uu____14512 =
          let uu____14514 =
            FStar_Util.for_all
              (fun uu____14528  ->
                 match uu____14528 with
                 | (uu____14538,uu____14539,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____14514  in
        if uu____14512
        then FStar_Pervasives_Native.None
        else
          (let norm c =
             (let uu____14591 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____14591
              then
                let uu____14594 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____14594
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____14601 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____14601
               then
                 let uu____14604 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____14604
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____14622 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____14622 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____14656 =
             match uu____14656 with
             | (lbname,e,c) ->
                 let c1 = norm c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____14693 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____14693
                   then
                     let uu____14698 =
                       let uu____14700 =
                         let uu____14704 = FStar_Util.set_elements univs  in
                         FStar_All.pipe_right uu____14704
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____14700
                         (FStar_String.concat ", ")
                        in
                     let uu____14760 =
                       let uu____14762 =
                         let uu____14766 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____14766
                           (FStar_List.map
                              (fun u  ->
                                 let uu____14779 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____14781 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____14779
                                   uu____14781))
                          in
                       FStar_All.pipe_right uu____14762
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____14698
                       uu____14760
                   else ());
                  (let univs1 =
                     let uu____14795 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs1  ->
                          fun uv  ->
                            let uu____14807 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs1 uu____14807) univs
                       uu____14795
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____14814 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____14814
                    then
                      let uu____14819 =
                        let uu____14821 =
                          let uu____14825 = FStar_Util.set_elements univs1
                             in
                          FStar_All.pipe_right uu____14825
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____14821
                          (FStar_String.concat ", ")
                         in
                      let uu____14881 =
                        let uu____14883 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____14897 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____14899 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____14897
                                    uu____14899))
                           in
                        FStar_All.pipe_right uu____14883
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____14819 uu____14881
                    else ());
                   (univs1, uvs, (lbname, e, c1))))
              in
           let uu____14920 =
             let uu____14937 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____14937  in
           match uu____14920 with
           | (univs,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____15027 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____15027
                 then ()
                 else
                   (let uu____15032 = lec_hd  in
                    match uu____15032 with
                    | (lb1,uu____15040,uu____15041) ->
                        let uu____15042 = lec2  in
                        (match uu____15042 with
                         | (lb2,uu____15050,uu____15051) ->
                             let msg =
                               let uu____15054 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15056 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____15054 uu____15056
                                in
                             let uu____15059 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____15059))
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
                 let uu____15127 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____15127
                 then ()
                 else
                   (let uu____15132 = lec_hd  in
                    match uu____15132 with
                    | (lb1,uu____15140,uu____15141) ->
                        let uu____15142 = lec2  in
                        (match uu____15142 with
                         | (lb2,uu____15150,uu____15151) ->
                             let msg =
                               let uu____15154 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15156 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____15154 uu____15156
                                in
                             let uu____15159 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____15159))
                  in
               let lecs1 =
                 let uu____15170 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____15223 = univs_and_uvars_of_lec this_lec  in
                        match uu____15223 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____15170 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail rng k =
                   let uu____15333 = lec_hd  in
                   match uu____15333 with
                   | (lbname,e,c) ->
                       let uu____15343 =
                         let uu____15349 =
                           let uu____15351 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____15353 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____15355 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____15351 uu____15353 uu____15355
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____15349)
                          in
                       FStar_Errors.raise_error uu____15343 rng
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____15377 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____15377 with
                         | FStar_Pervasives_Native.Some uu____15386 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____15394 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____15398 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____15398 with
                              | (bs,kres) ->
                                  ((let uu____15418 =
                                      let uu____15419 =
                                        let uu____15422 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____15422
                                         in
                                      uu____15419.FStar_Syntax_Syntax.n  in
                                    match uu____15418 with
                                    | FStar_Syntax_Syntax.Tm_type uu____15423
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____15427 =
                                          let uu____15429 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____15429  in
                                        if uu____15427
                                        then
                                          fail
                                            u.FStar_Syntax_Syntax.ctx_uvar_range
                                            kres
                                        else ()
                                    | uu____15434 ->
                                        fail
                                          u.FStar_Syntax_Syntax.ctx_uvar_range
                                          kres);
                                   (let a =
                                      let uu____15436 =
                                        let uu____15439 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun uu____15442  ->
                                             FStar_Pervasives_Native.Some
                                               uu____15442) uu____15439
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____15436
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____15450 ->
                                          let uu____15451 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____15451
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
                      (fun uu____15554  ->
                         match uu____15554 with
                         | (lbname,e,c) ->
                             let uu____15600 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____15661 ->
                                   let uu____15674 = (e, c)  in
                                   (match uu____15674 with
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
                                                (fun uu____15714  ->
                                                   match uu____15714 with
                                                   | (x,uu____15720) ->
                                                       let uu____15721 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____15721)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____15739 =
                                                let uu____15741 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____15741
                                                 in
                                              if uu____15739
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
                                          let uu____15750 =
                                            let uu____15751 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____15751.FStar_Syntax_Syntax.n
                                             in
                                          match uu____15750 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____15776 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____15776 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____15787 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____15791 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____15791, gen_tvars))
                                in
                             (match uu____15600 with
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
        (let uu____15938 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____15938
         then
           let uu____15941 =
             let uu____15943 =
               FStar_List.map
                 (fun uu____15958  ->
                    match uu____15958 with
                    | (lb,uu____15967,uu____15968) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____15943 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____15941
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____15994  ->
                match uu____15994 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____16023 = gen env is_rec lecs  in
           match uu____16023 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____16122  ->
                       match uu____16122 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____16184 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____16184
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____16232  ->
                           match uu____16232 with
                           | (l,us,e,c,gvs) ->
                               let uu____16266 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____16268 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____16270 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____16272 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____16274 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____16266 uu____16268 uu____16270
                                 uu____16272 uu____16274))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames  ->
              fun uu____16319  ->
                match uu____16319 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____16363 =
                      check_universe_generalization univnames
                        generalized_univs t
                       in
                    (l, uu____16363, t, c, gvs)) univnames_lecs
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
        let uu____16418 =
          let uu____16422 =
            let uu____16424 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____16424  in
          FStar_Pervasives_Native.Some uu____16422  in
        FStar_Profiling.profile
          (fun uu____16441  -> generalize' env is_rec lecs) uu____16418
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
              let uu____16498 =
                FStar_TypeChecker_Rel.get_teq_predicate env2 t1 t21  in
              match uu____16498 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some f ->
                  let uu____16504 = FStar_TypeChecker_Env.apply_guard f e  in
                  FStar_All.pipe_right uu____16504
                    (fun uu____16507  ->
                       FStar_Pervasives_Native.Some uu____16507)
            else
              if env2.FStar_TypeChecker_Env.use_eq
              then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
              else
                (let uu____16516 =
                   FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                    in
                 match uu____16516 with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some f ->
                     let uu____16522 = FStar_TypeChecker_Env.apply_guard f e
                        in
                     FStar_All.pipe_left
                       (fun uu____16525  ->
                          FStar_Pervasives_Native.Some uu____16525)
                       uu____16522)
             in
          let uu____16526 = maybe_coerce_lc env1 e lc t2  in
          match uu____16526 with
          | (e1,lc1,g_c) ->
              let uu____16542 =
                check env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____16542 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16551 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____16557 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____16551 uu____16557
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____16566 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____16566
                     then
                       let uu____16571 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____16571
                     else ());
                    (let uu____16577 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (e1, lc1, uu____16577))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____16605 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____16605
         then
           let uu____16608 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____16608
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____16622 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____16622 with
         | (c,g_c) ->
             let uu____16634 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____16634
             then
               let uu____16642 =
                 let uu____16644 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____16644  in
               (uu____16642, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____16652 =
                    let uu____16653 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____16653
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____16652
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____16654 = check_trivial_precondition env c1  in
                match uu____16654 with
                | (ct,vc,g_pre) ->
                    ((let uu____16670 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____16670
                      then
                        let uu____16675 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____16675
                      else ());
                     (let uu____16680 =
                        let uu____16682 =
                          let uu____16683 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____16683  in
                        discharge uu____16682  in
                      let uu____16684 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____16680, uu____16684)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head  ->
    fun seen_args  ->
      let short_bin_op f uu___8_16718 =
        match uu___8_16718 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst,uu____16728)::[] -> f fst
        | uu____16753 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____16765 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____16765
          (fun uu____16766  ->
             FStar_TypeChecker_Common.NonTrivial uu____16766)
         in
      let op_or_e e =
        let uu____16777 =
          let uu____16778 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____16778  in
        FStar_All.pipe_right uu____16777
          (fun uu____16781  ->
             FStar_TypeChecker_Common.NonTrivial uu____16781)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun uu____16788  ->
             FStar_TypeChecker_Common.NonTrivial uu____16788)
         in
      let op_or_t t =
        let uu____16799 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____16799
          (fun uu____16802  ->
             FStar_TypeChecker_Common.NonTrivial uu____16802)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun uu____16809  ->
             FStar_TypeChecker_Common.NonTrivial uu____16809)
         in
      let short_op_ite uu___9_16815 =
        match uu___9_16815 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____16825)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____16852)::[] ->
            let uu____16893 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____16893
              (fun uu____16894  ->
                 FStar_TypeChecker_Common.NonTrivial uu____16894)
        | uu____16895 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____16907 =
          let uu____16915 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____16915)  in
        let uu____16923 =
          let uu____16933 =
            let uu____16941 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____16941)  in
          let uu____16949 =
            let uu____16959 =
              let uu____16967 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____16967)  in
            let uu____16975 =
              let uu____16985 =
                let uu____16993 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____16993)  in
              let uu____17001 =
                let uu____17011 =
                  let uu____17019 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____17019)  in
                [uu____17011; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____16985 :: uu____17001  in
            uu____16959 :: uu____16975  in
          uu____16933 :: uu____16949  in
        uu____16907 :: uu____16923  in
      match head.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____17081 =
            FStar_Util.find_map table
              (fun uu____17096  ->
                 match uu____17096 with
                 | (x,mk) ->
                     let uu____17113 = FStar_Ident.lid_equals x lid  in
                     if uu____17113
                     then
                       let uu____17118 = mk seen_args  in
                       FStar_Pervasives_Native.Some uu____17118
                     else FStar_Pervasives_Native.None)
             in
          (match uu____17081 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____17122 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____17130 =
      let uu____17131 = FStar_Syntax_Util.un_uinst l  in
      uu____17131.FStar_Syntax_Syntax.n  in
    match uu____17130 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____17136 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd,uu____17172)::uu____17173 -> FStar_Syntax_Syntax.range_of_bv hd
        | uu____17192 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____17201,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____17202))::uu____17203 -> bs
      | uu____17221 ->
          let uu____17222 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____17222 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____17226 =
                 let uu____17227 = FStar_Syntax_Subst.compress t  in
                 uu____17227.FStar_Syntax_Syntax.n  in
               (match uu____17226 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____17231) ->
                    let uu____17252 =
                      FStar_Util.prefix_until
                        (fun uu___10_17292  ->
                           match uu___10_17292 with
                           | (uu____17300,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____17301)) ->
                               false
                           | uu____17306 -> true) bs'
                       in
                    (match uu____17252 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____17342,uu____17343) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____17415,uu____17416) ->
                         let uu____17489 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____17510  ->
                                   match uu____17510 with
                                   | (x,uu____17519) ->
                                       let uu____17524 =
                                         FStar_Ident.text_of_id
                                           x.FStar_Syntax_Syntax.ppname
                                          in
                                       FStar_Util.starts_with uu____17524 "'"))
                            in
                         if uu____17489
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____17570  ->
                                     match uu____17570 with
                                     | (x,i) ->
                                         let uu____17589 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____17589, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____17600 -> bs))
  
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
            let uu____17629 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____17629
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
          let uu____17660 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____17660
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
        (let uu____17703 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____17703
         then
           ((let uu____17708 = FStar_Ident.string_of_lid lident  in
             d uu____17708);
            (let uu____17710 = FStar_Ident.string_of_lid lident  in
             let uu____17712 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____17710 uu____17712))
         else ());
        (let fv =
           let uu____17718 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____17718
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
         let uu____17730 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___2072_17732 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2072_17732.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2072_17732.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2072_17732.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2072_17732.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2072_17732.FStar_Syntax_Syntax.sigopts)
           }), uu____17730))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_17750 =
        match uu___11_17750 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____17753 -> false  in
      let reducibility uu___12_17761 =
        match uu___12_17761 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____17768 -> false  in
      let assumption uu___13_17776 =
        match uu___13_17776 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____17780 -> false  in
      let reification uu___14_17788 =
        match uu___14_17788 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____17791 -> true
        | uu____17793 -> false  in
      let inferred uu___15_17801 =
        match uu___15_17801 with
        | FStar_Syntax_Syntax.Discriminator uu____17803 -> true
        | FStar_Syntax_Syntax.Projector uu____17805 -> true
        | FStar_Syntax_Syntax.RecordType uu____17811 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____17821 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____17834 -> false  in
      let has_eq uu___16_17842 =
        match uu___16_17842 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____17846 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____17925 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____17932 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____17965 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____17965))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____17996 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____17996
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
           | FStar_Syntax_Syntax.Sig_bundle uu____18016 ->
               let uu____18025 =
                 let uu____18027 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_18033  ->
                           match uu___17_18033 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____18036 -> false))
                    in
                 Prims.op_Negation uu____18027  in
               if uu____18025
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____18043 -> ()
           | FStar_Syntax_Syntax.Sig_fail uu____18050 -> ()
           | uu____18063 ->
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
      let uu____18077 =
        let uu____18079 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_18085  ->
                  match uu___18_18085 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____18088 -> false))
           in
        FStar_All.pipe_right uu____18079 Prims.op_Negation  in
      if uu____18077
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____18109 =
            let uu____18115 =
              let uu____18117 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____18117 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____18115)  in
          FStar_Errors.raise_error uu____18109 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____18135 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____18143 =
            let uu____18145 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____18145  in
          if uu____18143 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____18156),uu____18157) ->
              ((let uu____18169 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____18169
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____18178 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____18178
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____18189 ->
              ((let uu____18199 =
                  let uu____18201 =
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
                  Prims.op_Negation uu____18201  in
                if uu____18199 then err'1 () else ());
               (let uu____18211 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_18217  ->
                           match uu___19_18217 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____18220 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____18211
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____18226 ->
              let uu____18233 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____18233 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____18241 ->
              let uu____18248 =
                let uu____18250 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____18250  in
              if uu____18248 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____18260 ->
              let uu____18261 =
                let uu____18263 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____18263  in
              if uu____18261 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18273 ->
              let uu____18286 =
                let uu____18288 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____18288  in
              if uu____18286 then err'1 () else ()
          | uu____18298 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____18337 =
          let uu____18338 = FStar_Syntax_Subst.compress t1  in
          uu____18338.FStar_Syntax_Syntax.n  in
        match uu____18337 with
        | FStar_Syntax_Syntax.Tm_arrow uu____18342 ->
            let uu____18357 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____18357 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____18366;
               FStar_Syntax_Syntax.index = uu____18367;
               FStar_Syntax_Syntax.sort = t2;_},uu____18369)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head,uu____18378) -> descend env head
        | FStar_Syntax_Syntax.Tm_uinst (head,uu____18404) -> descend env head
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____18410 -> false
      
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
        (let uu____18420 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____18420
         then
           let uu____18425 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____18425
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
                  let uu____18490 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____18490 r  in
                let uu____18500 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____18500 with
                | (uu____18509,signature) ->
                    let uu____18511 =
                      let uu____18512 = FStar_Syntax_Subst.compress signature
                         in
                      uu____18512.FStar_Syntax_Syntax.n  in
                    (match uu____18511 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18520) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____18568 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____18584 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____18586 =
                                       FStar_Ident.string_of_lid eff_name  in
                                     let uu____18588 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____18584 uu____18586 uu____18588) r
                                 in
                              (match uu____18568 with
                               | (is,g) ->
                                   let uu____18601 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____18603 =
                                             let uu____18604 =
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
                                                 = uu____18604;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____18603
                                            in
                                         let uu____18623 =
                                           let uu____18630 =
                                             let uu____18631 =
                                               let uu____18646 =
                                                 let uu____18655 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_unit
                                                    in
                                                 [uu____18655]  in
                                               (uu____18646, eff_c)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____18631
                                              in
                                           FStar_Syntax_Syntax.mk uu____18630
                                            in
                                         uu____18623
                                           FStar_Pervasives_Native.None r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____18686 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____18686
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____18695 =
                                           let uu____18700 =
                                             FStar_List.map
                                               FStar_Syntax_Syntax.as_arg
                                               (a_tm :: is)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____18700
                                            in
                                         uu____18695
                                           FStar_Pervasives_Native.None r
                                      in
                                   (uu____18601, g))
                          | uu____18709 -> fail signature)
                     | uu____18710 -> fail signature)
  
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
            let uu____18741 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____18741
              (fun ed  ->
                 let uu____18749 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____18749 u a_tm)
  
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
              let uu____18785 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____18785 with
              | (uu____18790,sig_tm) ->
                  let fail t =
                    let uu____18798 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____18798 r  in
                  let uu____18804 =
                    let uu____18805 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____18805.FStar_Syntax_Syntax.n  in
                  (match uu____18804 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18809) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____18832)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____18854 -> fail sig_tm)
                   | uu____18855 -> fail sig_tm)
  
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
          (let uu____18886 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsApp")
              in
           if uu____18886
           then
             let uu____18891 = FStar_Syntax_Print.comp_to_string c  in
             let uu____18893 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____18891 uu____18893
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____18900 =
             let uu____18913 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____18914 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____18913, (ct.FStar_Syntax_Syntax.result_typ), uu____18914)
              in
           match uu____18900 with
           | (u,a,c_is) ->
               let uu____18972 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____18972 with
                | (uu____18981,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____18992 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____18994 = FStar_Ident.string_of_lid tgt  in
                      let uu____18996 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____18992 uu____18994 s uu____18996
                       in
                    let uu____18999 =
                      let uu____19032 =
                        let uu____19033 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____19033.FStar_Syntax_Syntax.n  in
                      match uu____19032 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____19097 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____19097 with
                           | (a_b::bs1,c2) ->
                               let uu____19157 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               (a_b, uu____19157, c2))
                      | uu____19245 ->
                          let uu____19246 =
                            let uu____19252 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____19252)
                             in
                          FStar_Errors.raise_error uu____19246 r
                       in
                    (match uu____18999 with
                     | (a_b,(rest_bs,f_b::[]),lift_c) ->
                         let uu____19370 =
                           let uu____19377 =
                             let uu____19378 =
                               let uu____19379 =
                                 let uu____19386 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____19386, a)  in
                               FStar_Syntax_Syntax.NT uu____19379  in
                             [uu____19378]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____19377
                             (fun b  ->
                                let uu____19403 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____19405 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____19407 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____19409 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit for binder %s of %s~>%s at %s"
                                  uu____19403 uu____19405 uu____19407
                                  uu____19409) r
                            in
                         (match uu____19370 with
                          | (rest_bs_uvars,g) ->
                              let substs =
                                FStar_List.map2
                                  (fun b  ->
                                     fun t  ->
                                       let uu____19446 =
                                         let uu____19453 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____19453, t)  in
                                       FStar_Syntax_Syntax.NT uu____19446)
                                  (a_b :: rest_bs) (a :: rest_bs_uvars)
                                 in
                              let guard_f =
                                let f_sort =
                                  let uu____19472 =
                                    FStar_All.pipe_right
                                      (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                      (FStar_Syntax_Subst.subst substs)
                                     in
                                  FStar_All.pipe_right uu____19472
                                    FStar_Syntax_Subst.compress
                                   in
                                let f_sort_is =
                                  let uu____19478 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env ct.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Syntax_Util.effect_indices_from_repr
                                    f_sort uu____19478 r
                                    "f binder of lift is not a repr"
                                   in
                                FStar_List.fold_left2
                                  (fun g1  ->
                                     fun i1  ->
                                       fun i2  ->
                                         (let uu____19498 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsRel")
                                             in
                                          if uu____19498
                                          then
                                            let uu____19503 =
                                              FStar_Syntax_Print.term_to_string
                                                i1
                                               in
                                            let uu____19505 =
                                              FStar_Syntax_Print.term_to_string
                                                i2
                                               in
                                            FStar_Util.print2
                                              "Layered Effects teq %s = %s\n"
                                              uu____19503 uu____19505
                                          else ());
                                         (let uu____19510 =
                                            FStar_TypeChecker_Rel.teq env i1
                                              i2
                                             in
                                          FStar_TypeChecker_Env.conj_guard g1
                                            uu____19510))
                                  FStar_TypeChecker_Env.trivial_guard c_is
                                  f_sort_is
                                 in
                              let lift_ct =
                                let uu____19512 =
                                  FStar_All.pipe_right lift_c
                                    (FStar_Syntax_Subst.subst_comp substs)
                                   in
                                FStar_All.pipe_right uu____19512
                                  FStar_Syntax_Util.comp_to_comp_typ
                                 in
                              let is =
                                let uu____19516 =
                                  FStar_TypeChecker_Env.is_layered_effect env
                                    tgt
                                   in
                                FStar_Syntax_Util.effect_indices_from_repr
                                  lift_ct.FStar_Syntax_Syntax.result_typ
                                  uu____19516 r
                                  "return type of lift is not a repr"
                                 in
                              let fml =
                                let uu____19520 =
                                  let uu____19525 =
                                    FStar_List.hd
                                      lift_ct.FStar_Syntax_Syntax.comp_univs
                                     in
                                  let uu____19526 =
                                    let uu____19527 =
                                      FStar_List.hd
                                        lift_ct.FStar_Syntax_Syntax.effect_args
                                       in
                                    FStar_Pervasives_Native.fst uu____19527
                                     in
                                  (uu____19525, uu____19526)  in
                                match uu____19520 with
                                | (u1,wp) ->
                                    FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                      env u1
                                      lift_ct.FStar_Syntax_Syntax.result_typ
                                      wp FStar_Range.dummyRange
                                 in
                              let c1 =
                                let uu____19551 =
                                  let uu____19552 =
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
                                      uu____19552;
                                    FStar_Syntax_Syntax.flags = []
                                  }  in
                                FStar_Syntax_Syntax.mk_Comp uu____19551  in
                              ((let uu____19576 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffectsApp")
                                   in
                                if uu____19576
                                then
                                  let uu____19581 =
                                    FStar_Syntax_Print.comp_to_string c1  in
                                  FStar_Util.print1 "} Lifted comp: %s\n"
                                    uu____19581
                                else ());
                               (let uu____19586 =
                                  let uu____19587 =
                                    FStar_TypeChecker_Env.conj_guard g
                                      guard_f
                                     in
                                  let uu____19588 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         fml)
                                     in
                                  FStar_TypeChecker_Env.conj_guard
                                    uu____19587 uu____19588
                                   in
                                (c1, uu____19586)))))))
  
let lift_tf_layered_effect_term :
  'uuuuuu19602 .
    'uuuuuu19602 ->
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
              let uu____19631 =
                let uu____19636 =
                  FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____19636
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____19631 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____19679 =
                let uu____19680 =
                  let uu____19683 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____19683
                    FStar_Syntax_Subst.compress
                   in
                uu____19680.FStar_Syntax_Syntax.n  in
              match uu____19679 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____19706::bs,uu____19708)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____19748 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____19748
                    FStar_Pervasives_Native.fst
              | uu____19854 ->
                  let uu____19855 =
                    let uu____19861 =
                      let uu____19863 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____19863
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____19861)  in
                  FStar_Errors.raise_error uu____19855
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____19890 = FStar_Syntax_Syntax.as_arg a  in
              let uu____19899 =
                let uu____19910 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____19946  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____19953 =
                  let uu____19964 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____19964]  in
                FStar_List.append uu____19910 uu____19953  in
              uu____19890 :: uu____19899  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index  ->
        let uu____20035 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____20035 with
        | (uu____20040,t) ->
            let err n =
              let uu____20050 =
                let uu____20056 =
                  let uu____20058 = FStar_Ident.string_of_lid datacon  in
                  let uu____20060 = FStar_Util.string_of_int n  in
                  let uu____20062 = FStar_Util.string_of_int index  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____20058 uu____20060 uu____20062
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____20056)
                 in
              let uu____20066 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____20050 uu____20066  in
            let uu____20067 =
              let uu____20068 = FStar_Syntax_Subst.compress t  in
              uu____20068.FStar_Syntax_Syntax.n  in
            (match uu____20067 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____20072) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____20127  ->
                           match uu____20127 with
                           | (uu____20135,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____20144 -> true)))
                    in
                 if (FStar_List.length bs1) <= index
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index  in
                    FStar_Syntax_Util.mk_field_projector_name datacon
                      (FStar_Pervasives_Native.fst b) index)
             | uu____20178 -> err Prims.int_zero)
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub  ->
      let uu____20191 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub.FStar_Syntax_Syntax.target)
         in
      if uu____20191
      then
        let uu____20194 =
          let uu____20207 =
            FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub.FStar_Syntax_Syntax.target uu____20207
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____20194;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____20242 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____20242 with
           | (uu____20251,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____20270 =
                 let uu____20271 =
                   let uu___2444_20272 = ct  in
                   let uu____20273 =
                     let uu____20284 =
                       let uu____20293 =
                         let uu____20294 =
                           let uu____20301 =
                             let uu____20302 =
                               let uu____20319 =
                                 let uu____20330 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____20330; wp]  in
                               (lift_t, uu____20319)  in
                             FStar_Syntax_Syntax.Tm_app uu____20302  in
                           FStar_Syntax_Syntax.mk uu____20301  in
                         uu____20294 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____20293
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____20284]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2444_20272.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2444_20272.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____20273;
                     FStar_Syntax_Syntax.flags =
                       (uu___2444_20272.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____20271  in
               (uu____20270, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____20430 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____20430 with
           | (uu____20437,lift_t) ->
               let uu____20439 =
                 let uu____20446 =
                   let uu____20447 =
                     let uu____20464 =
                       let uu____20475 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____20484 =
                         let uu____20495 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____20504 =
                           let uu____20515 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____20515]  in
                         uu____20495 :: uu____20504  in
                       uu____20475 :: uu____20484  in
                     (lift_t, uu____20464)  in
                   FStar_Syntax_Syntax.Tm_app uu____20447  in
                 FStar_Syntax_Syntax.mk uu____20446  in
               uu____20439 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____20568 =
           let uu____20581 =
             FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____20581 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____20568;
           FStar_TypeChecker_Env.mlift_term =
             (match sub.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____20617  ->
                        fun uu____20618  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun sub  ->
      let uu____20641 = get_mlift_for_subeff env sub  in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub.FStar_Syntax_Syntax.source sub.FStar_Syntax_Syntax.target
        uu____20641
  
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
  