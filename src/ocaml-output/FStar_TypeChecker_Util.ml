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
          let uu____87 = (FStar_Options.eager_subtyping ()) || solve_deferred
             in
          if uu____87
          then
            let uu____90 =
              FStar_All.pipe_right g.FStar_TypeChecker_Common.deferred
                (FStar_List.partition
                   (fun uu____142  ->
                      match uu____142 with
                      | (uu____149,p) ->
                          FStar_TypeChecker_Rel.flex_prob_closing env xs p))
               in
            match uu____90 with
            | (solve_now,defer) ->
                ((let uu____184 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel")
                     in
                  if uu____184
                  then
                    (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                     FStar_List.iter
                       (fun uu____201  ->
                          match uu____201 with
                          | (s,p) ->
                              let uu____211 =
                                FStar_TypeChecker_Rel.prob_to_string env p
                                 in
                              FStar_Util.print2 "%s: %s\n" s uu____211)
                       solve_now;
                     FStar_Util.print_string " ...DEFERRED THE REST:\n";
                     FStar_List.iter
                       (fun uu____226  ->
                          match uu____226 with
                          | (s,p) ->
                              let uu____236 =
                                FStar_TypeChecker_Rel.prob_to_string env p
                                 in
                              FStar_Util.print2 "%s: %s\n" s uu____236) defer;
                     FStar_Util.print_string "END\n")
                  else ());
                 (let g1 =
                    FStar_TypeChecker_Rel.solve_deferred_constraints env
                      (let uu___49_244 = g  in
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
                       })
                     in
                  let g2 =
                    let uu___52_246 = g1  in
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
                    }  in
                  g2))
          else g
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____263 =
        let uu____265 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____265  in
      if uu____263
      then
        let us =
          let uu____270 =
            let uu____274 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____274
             in
          FStar_All.pipe_right uu____270 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____293 =
            let uu____299 =
              let uu____301 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____301
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____299)  in
          FStar_Errors.log_issue r uu____293);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool))
  =
  fun env  ->
    fun uu____324  ->
      match uu____324 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____335;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____337;
          FStar_Syntax_Syntax.lbpos = uu____338;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____373 = FStar_Syntax_Subst.open_univ_vars univ_vars e
                  in
               (match uu____373 with
                | (univ_vars1,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____411) -> aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____418) ->
                          FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____473) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____509 = FStar_Options.ml_ish ()  in
                                if uu____509
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____531 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____531
                            then
                              let uu____534 = FStar_Range.string_of_range r
                                 in
                              let uu____536 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____534 uu____536
                            else ());
                           FStar_Util.Inl t2)
                      | uu____541 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____543 = aux e1  in
                      match uu____543 with
                      | FStar_Util.Inr c ->
                          let uu____549 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____549
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____554 =
                               let uu____560 =
                                 let uu____562 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____562
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____560)
                                in
                             FStar_Errors.raise_error uu____554 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars1, t2, true))
           | uu____571 ->
               let uu____572 = FStar_Syntax_Subst.open_univ_vars univ_vars t1
                  in
               (match uu____572 with
                | (univ_vars1,t2) -> (univ_vars1, t2, false)))
  
let rec (decorated_pattern_as_term :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun pat  ->
    let mk f = FStar_Syntax_Syntax.mk f pat.FStar_Syntax_Syntax.p  in
    let pat_as_arg uu____636 =
      match uu____636 with
      | (p,i) ->
          let uu____656 = decorated_pattern_as_term p  in
          (match uu____656 with
           | (vars,te) ->
               let uu____679 =
                 let uu____684 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____684)  in
               (vars, uu____679))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____698 = mk (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____698)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____702 = mk (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____702)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____706 = mk (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____706)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____729 =
          let uu____748 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____748 FStar_List.unzip  in
        (match uu____729 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____886 =
               let uu____887 =
                 let uu____888 =
                   let uu____905 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____905, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____888  in
               mk uu____887  in
             (vars1, uu____886))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____944,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____954,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd::uu____968 -> FStar_Pervasives_Native.Some hd)
  
let (lcomp_univ_opt :
  FStar_TypeChecker_Common.lcomp ->
    (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option *
      FStar_TypeChecker_Common.guard_t))
  =
  fun lc  ->
    let uu____983 =
      FStar_All.pipe_right lc FStar_TypeChecker_Common.lcomp_comp  in
    FStar_All.pipe_right uu____983
      (fun uu____1011  ->
         match uu____1011 with | (c,g) -> ((comp_univ_opt c), g))
  
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
            let uu____1084 =
              let uu____1085 =
                let uu____1096 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____1096]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____1085;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____1084
  
let (mk_comp :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  = fun md  -> mk_comp_l md.FStar_Syntax_Syntax.mname 
let (effect_args_from_repr :
  FStar_Syntax_Syntax.term ->
    Prims.bool -> FStar_Range.range -> FStar_Syntax_Syntax.term Prims.list)
  =
  fun repr  ->
    fun is_layered  ->
      fun r  ->
        let err uu____1180 =
          let uu____1181 =
            let uu____1187 =
              let uu____1189 = FStar_Syntax_Print.term_to_string repr  in
              let uu____1191 = FStar_Util.string_of_bool is_layered  in
              FStar_Util.format2
                "Could not get effect args from repr %s with is_layered %s"
                uu____1189 uu____1191
               in
            (FStar_Errors.Fatal_UnexpectedEffect, uu____1187)  in
          FStar_Errors.raise_error uu____1181 r  in
        let repr1 = FStar_Syntax_Subst.compress repr  in
        if is_layered
        then
          match repr1.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_app (uu____1203,uu____1204::is) ->
              FStar_All.pipe_right is
                (FStar_List.map FStar_Pervasives_Native.fst)
          | uu____1272 -> err ()
        else
          (match repr1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (uu____1277,c) ->
               let uu____1299 =
                 FStar_All.pipe_right c FStar_Syntax_Util.comp_to_comp_typ
                  in
               FStar_All.pipe_right uu____1299
                 (fun ct  ->
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
                let uu____1368 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_a] env ed
                    ret_wp
                   in
                let uu____1369 =
                  let uu____1370 = FStar_Syntax_Syntax.as_arg a  in
                  let uu____1379 =
                    let uu____1390 = FStar_Syntax_Syntax.as_arg e  in
                    [uu____1390]  in
                  uu____1370 :: uu____1379  in
                FStar_Syntax_Syntax.mk_Tm_app uu____1368 uu____1369 r  in
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
              (let uu____1463 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "LayeredEffects")
                  in
               if uu____1463
               then
                 let uu____1468 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname  in
                 let uu____1470 = FStar_Syntax_Print.univ_to_string u_a  in
                 let uu____1472 = FStar_Syntax_Print.term_to_string a  in
                 let uu____1474 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print4
                   "Computing %s.return for u_a:%s, a:%s, and e:%s{\n"
                   uu____1468 uu____1470 uu____1472 uu____1474
               else ());
              (let uu____1479 =
                 let uu____1484 =
                   FStar_All.pipe_right ed
                     FStar_Syntax_Util.get_return_vc_combinator
                    in
                 FStar_TypeChecker_Env.inst_tscheme_with uu____1484 [u_a]  in
               match uu____1479 with
               | (uu____1489,return_t) ->
                   let return_t_shape_error s =
                     let uu____1504 =
                       let uu____1506 =
                         FStar_Ident.string_of_lid
                           ed.FStar_Syntax_Syntax.mname
                          in
                       let uu____1508 =
                         FStar_Syntax_Print.term_to_string return_t  in
                       FStar_Util.format3
                         "%s.return %s does not have proper shape (reason:%s)"
                         uu____1506 uu____1508 s
                        in
                     (FStar_Errors.Fatal_UnexpectedEffect, uu____1504)  in
                   let uu____1512 =
                     let uu____1541 =
                       let uu____1542 = FStar_Syntax_Subst.compress return_t
                          in
                       uu____1542.FStar_Syntax_Syntax.n  in
                     match uu____1541 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                         (FStar_List.length bs) >= (Prims.of_int (2)) ->
                         let uu____1602 = FStar_Syntax_Subst.open_comp bs c
                            in
                         (match uu____1602 with
                          | (a_b::x_b::bs1,c1) ->
                              let uu____1671 =
                                FStar_Syntax_Util.comp_to_comp_typ c1  in
                              (a_b, x_b, bs1, uu____1671))
                     | uu____1692 ->
                         let uu____1693 =
                           return_t_shape_error
                             "Either not an arrow or not enough binders"
                            in
                         FStar_Errors.raise_error uu____1693 r
                      in
                   (match uu____1512 with
                    | (a_b,x_b,rest_bs,return_ct) ->
                        let uu____1776 =
                          let uu____1783 =
                            let uu____1784 =
                              let uu____1785 =
                                let uu____1792 =
                                  FStar_All.pipe_right a_b
                                    FStar_Pervasives_Native.fst
                                   in
                                (uu____1792, a)  in
                              FStar_Syntax_Syntax.NT uu____1785  in
                            let uu____1803 =
                              let uu____1806 =
                                let uu____1807 =
                                  let uu____1814 =
                                    FStar_All.pipe_right x_b
                                      FStar_Pervasives_Native.fst
                                     in
                                  (uu____1814, e)  in
                                FStar_Syntax_Syntax.NT uu____1807  in
                              [uu____1806]  in
                            uu____1784 :: uu____1803  in
                          FStar_TypeChecker_Env.uvars_for_binders env rest_bs
                            uu____1783
                            (fun b  ->
                               let uu____1830 =
                                 FStar_Syntax_Print.binder_to_string b  in
                               let uu____1832 =
                                 let uu____1834 =
                                   FStar_Ident.string_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Util.format1 "%s.return" uu____1834
                                  in
                               let uu____1837 = FStar_Range.string_of_range r
                                  in
                               FStar_Util.format3
                                 "implicit var for binder %s of %s at %s"
                                 uu____1830 uu____1832 uu____1837) r
                           in
                        (match uu____1776 with
                         | (rest_bs_uvars,g_uvars) ->
                             let subst =
                               FStar_List.map2
                                 (fun b  ->
                                    fun t  ->
                                      let uu____1874 =
                                        let uu____1881 =
                                          FStar_All.pipe_right b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____1881, t)  in
                                      FStar_Syntax_Syntax.NT uu____1874) (a_b
                                 :: x_b :: rest_bs) (a :: e :: rest_bs_uvars)
                                in
                             let is =
                               let uu____1907 =
                                 let uu____1910 =
                                   FStar_Syntax_Subst.compress
                                     return_ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 let uu____1911 =
                                   FStar_Syntax_Util.is_layered ed  in
                                 effect_args_from_repr uu____1910 uu____1911
                                   r
                                  in
                               FStar_All.pipe_right uu____1907
                                 (FStar_List.map
                                    (FStar_Syntax_Subst.subst subst))
                                in
                             let c =
                               let uu____1918 =
                                 let uu____1919 =
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
                                     uu____1919;
                                   FStar_Syntax_Syntax.flags = []
                                 }  in
                               FStar_Syntax_Syntax.mk_Comp uu____1918  in
                             ((let uu____1943 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____1943
                               then
                                 let uu____1948 =
                                   FStar_Syntax_Print.comp_to_string c  in
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
  fun env  ->
    fun ed  ->
      fun u_a  ->
        fun a  ->
          fun e  ->
            fun r  ->
              let uu____1992 =
                FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
              if uu____1992
              then mk_indexed_return env ed u_a a e r
              else
                (let uu____2002 = mk_wp_return env ed u_a a e r  in
                 (uu____2002, FStar_TypeChecker_Env.trivial_guard))
  
let (lift_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp_typ ->
      FStar_TypeChecker_Env.mlift ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c  ->
      fun lift  ->
        let uu____2027 =
          FStar_All.pipe_right
            (let uu___251_2029 = c  in
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
             }) FStar_Syntax_Syntax.mk_Comp
           in
        FStar_All.pipe_right uu____2027
          (lift.FStar_TypeChecker_Env.mlift_wp env)
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1_in  ->
      fun l2_in  ->
        let uu____2050 =
          let uu____2055 = FStar_TypeChecker_Env.norm_eff_name env l1_in  in
          let uu____2056 = FStar_TypeChecker_Env.norm_eff_name env l2_in  in
          (uu____2055, uu____2056)  in
        match uu____2050 with
        | (l1,l2) ->
            let uu____2059 = FStar_TypeChecker_Env.join_opt env l1 l2  in
            (match uu____2059 with
             | FStar_Pervasives_Native.Some (m,uu____2069,uu____2070) -> m
             | FStar_Pervasives_Native.None  ->
                 let uu____2083 =
                   FStar_TypeChecker_Env.exists_polymonadic_bind env l1 l2
                    in
                 (match uu____2083 with
                  | FStar_Pervasives_Native.Some (m,uu____2097) -> m
                  | FStar_Pervasives_Native.None  ->
                      let uu____2130 =
                        let uu____2136 =
                          let uu____2138 =
                            FStar_Syntax_Print.lid_to_string l1_in  in
                          let uu____2140 =
                            FStar_Syntax_Print.lid_to_string l2_in  in
                          FStar_Util.format2
                            "Effects %s and %s cannot be composed" uu____2138
                            uu____2140
                           in
                        (FStar_Errors.Fatal_EffectsCannotBeComposed,
                          uu____2136)
                         in
                      FStar_Errors.raise_error uu____2130
                        env.FStar_TypeChecker_Env.range))
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2160 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2)
           in
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
  fun env  ->
    fun c1  ->
      fun c2  ->
        fun b  ->
          fun for_bind  ->
            let c11 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
            let c21 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
            let uu____2219 =
              FStar_TypeChecker_Env.join_opt env
                c11.FStar_Syntax_Syntax.effect_name
                c21.FStar_Syntax_Syntax.effect_name
               in
            match uu____2219 with
            | FStar_Pervasives_Native.Some (m,lift1,lift2) ->
                let uu____2247 = lift_comp env c11 lift1  in
                (match uu____2247 with
                 | (c12,g1) ->
                     let uu____2264 =
                       if Prims.op_Negation for_bind
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
                          let uu____2303 = lift_comp env_x c21 lift2  in
                          match uu____2303 with
                          | (c22,g2) ->
                              let uu____2314 =
                                FStar_TypeChecker_Env.close_guard env 
                                  [x_a] g2
                                 in
                              (c22, uu____2314))
                        in
                     (match uu____2264 with
                      | (c22,g2) -> (m, c12, c22, g1, g2)))
            | FStar_Pervasives_Native.None  ->
                let uu____2345 =
                  let uu____2351 =
                    let uu____2353 =
                      FStar_Syntax_Print.lid_to_string
                        c11.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____2355 =
                      FStar_Syntax_Print.lid_to_string
                        c21.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "Effects %s and %s cannot be composed"
                      uu____2353 uu____2355
                     in
                  (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____2351)
                   in
                FStar_Errors.raise_error uu____2345
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
  fun env  ->
    fun c1  ->
      fun c2  ->
        fun b  ->
          fun for_bind  ->
            let uu____2417 = lift_comps_sep_guards env c1 c2 b for_bind  in
            match uu____2417 with
            | (l,c11,c21,g1,g2) ->
                let uu____2441 = FStar_TypeChecker_Env.conj_guard g1 g2  in
                (l, c11, c21, uu____2441)
  
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
          let uu____2497 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____2497
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2509 =
      let uu____2510 = FStar_Syntax_Subst.compress t  in
      uu____2510.FStar_Syntax_Syntax.n  in
    match uu____2509 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2514 -> true
    | uu____2530 -> false
  
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
          f.FStar_Syntax_Syntax.pos
  
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
              let uu____2600 =
                let uu____2602 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____2602  in
              if uu____2600
              then f
              else (let uu____2609 = reason1 ()  in label uu____2609 r f)
  
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
            let uu___345_2630 = g  in
            let uu____2631 =
              let uu____2632 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____2632  in
            {
              FStar_TypeChecker_Common.guard_f = uu____2631;
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___345_2630.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___345_2630.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___345_2630.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___345_2630.FStar_TypeChecker_Common.implicits)
            }
  
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2653 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____2653
        then c
        else
          (let uu____2658 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____2658
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close =
                  let uu____2700 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator
                     in
                  FStar_All.pipe_right uu____2700 FStar_Util.must  in
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____2729 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____2729]  in
                       let us =
                         let uu____2751 =
                           let uu____2754 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____2754]  in
                         u_res :: uu____2751  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____2760 =
                         FStar_TypeChecker_Env.inst_effect_fun_with us env md
                           close
                          in
                       let uu____2761 =
                         let uu____2762 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____2771 =
                           let uu____2782 =
                             FStar_Syntax_Syntax.as_arg
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____2791 =
                             let uu____2802 = FStar_Syntax_Syntax.as_arg wp1
                                in
                             [uu____2802]  in
                           uu____2782 :: uu____2791  in
                         uu____2762 :: uu____2771  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____2760 uu____2761
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____2844 = destruct_wp_comp c1  in
              match uu____2844 with
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
                let uu____2884 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____2884
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
                  let uu____2934 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs)
                     in
                  FStar_All.pipe_right uu____2934
                    (close_guard_implicits env false bs)))
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_2947  ->
            match uu___0_2947 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____2950 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____2975 =
            let uu____2978 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____2978 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____2975
            (fun c  ->
               (let uu____3002 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____3002) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____3006 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____3006)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____3017 = FStar_Syntax_Util.head_and_args' e  in
                match uu____3017 with
                | (head,uu____3034) ->
                    let uu____3055 =
                      let uu____3056 = FStar_Syntax_Util.un_uinst head  in
                      uu____3056.FStar_Syntax_Syntax.n  in
                    (match uu____3055 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____3061 =
                           let uu____3063 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____3063
                            in
                         Prims.op_Negation uu____3061
                     | uu____3064 -> true)))
              &&
              (let uu____3067 = should_not_inline_lc lc  in
               Prims.op_Negation uu____3067)
  
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
            let uu____3095 =
              let uu____3097 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____3097  in
            if uu____3095
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____3104 = FStar_Syntax_Util.is_unit t  in
               if uu____3104
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
                    let uu____3113 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____3113
                    then FStar_Syntax_Syntax.tun
                    else
                      (let ret_wp =
                         FStar_All.pipe_right m
                           FStar_Syntax_Util.get_return_vc_combinator
                          in
                       let uu____3119 =
                         let uu____3120 =
                           FStar_TypeChecker_Env.inst_effect_fun_with 
                             [u_t] env m ret_wp
                            in
                         let uu____3121 =
                           let uu____3122 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____3131 =
                             let uu____3142 = FStar_Syntax_Syntax.as_arg v
                                in
                             [uu____3142]  in
                           uu____3122 :: uu____3131  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3120 uu____3121
                           v.FStar_Syntax_Syntax.pos
                          in
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Env.Beta;
                         FStar_TypeChecker_Env.NoFullNorm] env uu____3119)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____3176 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____3176
           then
             let uu____3181 =
               FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos  in
             let uu____3183 = FStar_Syntax_Print.term_to_string v  in
             let uu____3185 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____3181 uu____3183 uu____3185
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
                      let bind_name =
                        let uu____3259 =
                          let uu____3261 =
                            FStar_All.pipe_right m FStar_Ident.ident_of_lid
                             in
                          FStar_All.pipe_right uu____3261
                            FStar_Ident.string_of_id
                           in
                        let uu____3263 =
                          let uu____3265 =
                            FStar_All.pipe_right n FStar_Ident.ident_of_lid
                             in
                          FStar_All.pipe_right uu____3265
                            FStar_Ident.string_of_id
                           in
                        let uu____3267 =
                          let uu____3269 =
                            FStar_All.pipe_right p FStar_Ident.ident_of_lid
                             in
                          FStar_All.pipe_right uu____3269
                            FStar_Ident.string_of_id
                           in
                        FStar_Util.format3 "(%s, %s) |> %s" uu____3259
                          uu____3263 uu____3267
                         in
                      (let uu____3273 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LayeredEffects")
                          in
                       if uu____3273
                       then
                         let uu____3278 =
                           let uu____3280 = FStar_Syntax_Syntax.mk_Comp ct1
                              in
                           FStar_Syntax_Print.comp_to_string uu____3280  in
                         let uu____3281 =
                           let uu____3283 = FStar_Syntax_Syntax.mk_Comp ct2
                              in
                           FStar_Syntax_Print.comp_to_string uu____3283  in
                         FStar_Util.print2 "Binding c1:%s and c2:%s {\n"
                           uu____3278 uu____3281
                       else ());
                      (let uu____3288 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "ResolveImplicitsHook")
                          in
                       if uu____3288
                       then
                         let uu____3293 =
                           let uu____3295 =
                             FStar_TypeChecker_Env.get_range env  in
                           FStar_Range.string_of_range uu____3295  in
                         let uu____3296 =
                           FStar_Syntax_Print.tscheme_to_string bind_t  in
                         FStar_Util.print2
                           "///////////////////////////////Bind at %s/////////////////////\nwith bind_t = %s\n"
                           uu____3293 uu____3296
                       else ());
                      (let uu____3301 =
                         let uu____3308 =
                           FStar_TypeChecker_Env.get_effect_decl env m  in
                         let uu____3309 =
                           FStar_TypeChecker_Env.get_effect_decl env n  in
                         let uu____3310 =
                           FStar_TypeChecker_Env.get_effect_decl env p  in
                         (uu____3308, uu____3309, uu____3310)  in
                       match uu____3301 with
                       | (m_ed,n_ed,p_ed) ->
                           let uu____3318 =
                             let uu____3331 =
                               FStar_List.hd
                                 ct1.FStar_Syntax_Syntax.comp_univs
                                in
                             let uu____3332 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 ct1.FStar_Syntax_Syntax.effect_args
                                in
                             (uu____3331,
                               (ct1.FStar_Syntax_Syntax.result_typ),
                               uu____3332)
                              in
                           (match uu____3318 with
                            | (u1,t1,is1) ->
                                let uu____3376 =
                                  let uu____3389 =
                                    FStar_List.hd
                                      ct2.FStar_Syntax_Syntax.comp_univs
                                     in
                                  let uu____3390 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst
                                      ct2.FStar_Syntax_Syntax.effect_args
                                     in
                                  (uu____3389,
                                    (ct2.FStar_Syntax_Syntax.result_typ),
                                    uu____3390)
                                   in
                                (match uu____3376 with
                                 | (u2,t2,is2) ->
                                     let uu____3434 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         bind_t [u1; u2]
                                        in
                                     (match uu____3434 with
                                      | (uu____3443,bind_t1) ->
                                          let bind_t_shape_error s =
                                            let uu____3458 =
                                              let uu____3460 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t1
                                                 in
                                              FStar_Util.format3
                                                "bind %s (%s) does not have proper shape (reason:%s)"
                                                uu____3460 bind_name s
                                               in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu____3458)
                                             in
                                          let uu____3464 =
                                            let uu____3509 =
                                              let uu____3510 =
                                                FStar_Syntax_Subst.compress
                                                  bind_t1
                                                 in
                                              uu____3510.FStar_Syntax_Syntax.n
                                               in
                                            match uu____3509 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs,c) when
                                                (FStar_List.length bs) >=
                                                  (Prims.of_int (4))
                                                ->
                                                let uu____3586 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs c
                                                   in
                                                (match uu____3586 with
                                                 | (a_b::b_b::bs1,c1) ->
                                                     let uu____3671 =
                                                       let uu____3698 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2)))
                                                           bs1
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____3698
                                                         (fun uu____3783  ->
                                                            match uu____3783
                                                            with
                                                            | (l1,l2) ->
                                                                let uu____3864
                                                                  =
                                                                  FStar_List.hd
                                                                    l2
                                                                   in
                                                                let uu____3877
                                                                  =
                                                                  let uu____3884
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                  FStar_List.hd
                                                                    uu____3884
                                                                   in
                                                                (l1,
                                                                  uu____3864,
                                                                  uu____3877))
                                                        in
                                                     (match uu____3671 with
                                                      | (rest_bs,f_b,g_b) ->
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b, c1)))
                                            | uu____4044 ->
                                                let uu____4045 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders"
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____4045 r1
                                             in
                                          (match uu____3464 with
                                           | (a_b,b_b,rest_bs,f_b,g_b,bind_c)
                                               ->
                                               let uu____4170 =
                                                 let uu____4177 =
                                                   let uu____4178 =
                                                     let uu____4179 =
                                                       let uu____4186 =
                                                         FStar_All.pipe_right
                                                           a_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       (uu____4186, t1)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____4179
                                                      in
                                                   let uu____4197 =
                                                     let uu____4200 =
                                                       let uu____4201 =
                                                         let uu____4208 =
                                                           FStar_All.pipe_right
                                                             b_b
                                                             FStar_Pervasives_Native.fst
                                                            in
                                                         (uu____4208, t2)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____4201
                                                        in
                                                     [uu____4200]  in
                                                   uu____4178 :: uu____4197
                                                    in
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs uu____4177
                                                   (fun b1  ->
                                                      let uu____4223 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1
                                                         in
                                                      let uu____4225 =
                                                        FStar_Range.string_of_range
                                                          r1
                                                         in
                                                      FStar_Util.format3
                                                        "implicit var for binder %s of %s at %s"
                                                        uu____4223 bind_name
                                                        uu____4225) r1
                                                  in
                                               (match uu____4170 with
                                                | (rest_bs_uvars,g_uvars) ->
                                                    ((let uu____4239 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "ResolveImplicitsHook")
                                                         in
                                                      if uu____4239
                                                      then
                                                        FStar_All.pipe_right
                                                          rest_bs_uvars
                                                          (FStar_List.iter
                                                             (fun t  ->
                                                                let uu____4253
                                                                  =
                                                                  let uu____4254
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    t  in
                                                                  uu____4254.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____4253
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (u,uu____4258)
                                                                    ->
                                                                    let uu____4275
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t  in
                                                                    let uu____4277
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
                                                                    uu____4283
                                                                    ->
                                                                    "<no attr>"
                                                                     in
                                                                    FStar_Util.print2
                                                                    "Generated uvar %s with attribute %s\n"
                                                                    uu____4275
                                                                    uu____4277))
                                                      else ());
                                                     (let subst =
                                                        FStar_List.map2
                                                          (fun b1  ->
                                                             fun t  ->
                                                               let uu____4314
                                                                 =
                                                                 let uu____4321
                                                                   =
                                                                   FStar_All.pipe_right
                                                                    b1
                                                                    FStar_Pervasives_Native.fst
                                                                    in
                                                                 (uu____4321,
                                                                   t)
                                                                  in
                                                               FStar_Syntax_Syntax.NT
                                                                 uu____4314)
                                                          (a_b :: b_b ::
                                                          rest_bs) (t1 :: t2
                                                          :: rest_bs_uvars)
                                                         in
                                                      let f_guard =
                                                        let f_sort_is =
                                                          let uu____4350 =
                                                            let uu____4353 =
                                                              let uu____4354
                                                                =
                                                                let uu____4355
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    f_b
                                                                    FStar_Pervasives_Native.fst
                                                                   in
                                                                uu____4355.FStar_Syntax_Syntax.sort
                                                                 in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4354
                                                               in
                                                            let uu____4364 =
                                                              FStar_Syntax_Util.is_layered
                                                                m_ed
                                                               in
                                                            effect_args_from_repr
                                                              uu____4353
                                                              uu____4364 r1
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____4350
                                                            (FStar_List.map
                                                               (FStar_Syntax_Subst.subst
                                                                  subst))
                                                           in
                                                        FStar_List.fold_left2
                                                          (fun g  ->
                                                             fun i1  ->
                                                               fun f_i1  ->
                                                                 (let uu____4389
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "ResolveImplicitsHook")
                                                                     in
                                                                  if
                                                                    uu____4389
                                                                  then
                                                                    let uu____4394
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    i1  in
                                                                    let uu____4396
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    f_i1  in
                                                                    FStar_Util.print2
                                                                    "Generating constraint %s = %s\n"
                                                                    uu____4394
                                                                    uu____4396
                                                                  else ());
                                                                 (let uu____4401
                                                                    =
                                                                    FStar_TypeChecker_Rel.layered_effect_teq
                                                                    env i1
                                                                    f_i1
                                                                    (FStar_Pervasives_Native.Some
                                                                    bind_name)
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____4401))
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
                                                          let uu____4421 =
                                                            let uu____4422 =
                                                              let uu____4425
                                                                =
                                                                let uu____4426
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    g_b
                                                                    FStar_Pervasives_Native.fst
                                                                   in
                                                                uu____4426.FStar_Syntax_Syntax.sort
                                                                 in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4425
                                                               in
                                                            uu____4422.FStar_Syntax_Syntax.n
                                                             in
                                                          match uu____4421
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_arrow
                                                              (bs,c) ->
                                                              let uu____4459
                                                                =
                                                                FStar_Syntax_Subst.open_comp
                                                                  bs c
                                                                 in
                                                              (match uu____4459
                                                               with
                                                               | (bs1,c1) ->
                                                                   let bs_subst
                                                                    =
                                                                    let uu____4469
                                                                    =
                                                                    let uu____4476
                                                                    =
                                                                    let uu____4477
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____4477
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____4498
                                                                    =
                                                                    let uu____4501
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4501
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____4476,
                                                                    uu____4498)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4469
                                                                     in
                                                                   let c2 =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1  in
                                                                   let uu____4515
                                                                    =
                                                                    let uu____4518
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2)  in
                                                                    let uu____4519
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed  in
                                                                    effect_args_from_repr
                                                                    uu____4518
                                                                    uu____4519
                                                                    r1  in
                                                                   FStar_All.pipe_right
                                                                    uu____4515
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst)))
                                                          | uu____4525 ->
                                                              failwith
                                                                "impossible: mk_indexed_bind"
                                                           in
                                                        let env_g =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env [x_a]
                                                           in
                                                        let uu____4542 =
                                                          FStar_List.fold_left2
                                                            (fun g  ->
                                                               fun i1  ->
                                                                 fun g_i1  ->
                                                                   (let uu____4560
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "ResolveImplicitsHook")
                                                                     in
                                                                    if
                                                                    uu____4560
                                                                    then
                                                                    let uu____4565
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    i1  in
                                                                    let uu____4567
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    g_i1  in
                                                                    FStar_Util.print2
                                                                    "Generating constraint %s = %s\n"
                                                                    uu____4565
                                                                    uu____4567
                                                                    else ());
                                                                   (let uu____4572
                                                                    =
                                                                    FStar_TypeChecker_Rel.layered_effect_teq
                                                                    env_g i1
                                                                    g_i1
                                                                    (FStar_Pervasives_Native.Some
                                                                    bind_name)
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____4572))
                                                            FStar_TypeChecker_Env.trivial_guard
                                                            is2 g_sort_is
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____4542
                                                          (FStar_TypeChecker_Env.close_guard
                                                             env [x_a])
                                                         in
                                                      let bind_ct =
                                                        let uu____4587 =
                                                          FStar_All.pipe_right
                                                            bind_c
                                                            (FStar_Syntax_Subst.subst_comp
                                                               subst)
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____4587
                                                          FStar_Syntax_Util.comp_to_comp_typ
                                                         in
                                                      let fml =
                                                        let uu____4589 =
                                                          let uu____4594 =
                                                            FStar_List.hd
                                                              bind_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____4595 =
                                                            let uu____4596 =
                                                              FStar_List.hd
                                                                bind_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____4596
                                                             in
                                                          (uu____4594,
                                                            uu____4595)
                                                           in
                                                        match uu____4589 with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              bind_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let is =
                                                        let uu____4622 =
                                                          FStar_Syntax_Subst.compress
                                                            bind_ct.FStar_Syntax_Syntax.result_typ
                                                           in
                                                        let uu____4623 =
                                                          FStar_Syntax_Util.is_layered
                                                            p_ed
                                                           in
                                                        effect_args_from_repr
                                                          uu____4622
                                                          uu____4623 r1
                                                         in
                                                      let c =
                                                        let uu____4626 =
                                                          let uu____4627 =
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
                                                              = uu____4627;
                                                            FStar_Syntax_Syntax.flags
                                                              = flags
                                                          }  in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____4626
                                                         in
                                                      (let uu____4647 =
                                                         FStar_All.pipe_left
                                                           (FStar_TypeChecker_Env.debug
                                                              env)
                                                           (FStar_Options.Other
                                                              "LayeredEffects")
                                                          in
                                                       if uu____4647
                                                       then
                                                         let uu____4652 =
                                                           FStar_Syntax_Print.comp_to_string
                                                             c
                                                            in
                                                         FStar_Util.print1
                                                           "} c after bind: %s\n"
                                                           uu____4652
                                                       else ());
                                                      (let guard =
                                                         let uu____4658 =
                                                           let uu____4661 =
                                                             let uu____4664 =
                                                               let uu____4667
                                                                 =
                                                                 let uu____4670
                                                                   =
                                                                   FStar_TypeChecker_Env.guard_of_guard_formula
                                                                    (FStar_TypeChecker_Common.NonTrivial
                                                                    fml)
                                                                    in
                                                                 [uu____4670]
                                                                  in
                                                               g_guard ::
                                                                 uu____4667
                                                                in
                                                             f_guard ::
                                                               uu____4664
                                                              in
                                                           g_uvars ::
                                                             uu____4661
                                                            in
                                                         FStar_TypeChecker_Env.conj_guards
                                                           uu____4658
                                                          in
                                                       (let uu____4672 =
                                                          FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "ResolveImplicitsHook")
                                                           in
                                                        if uu____4672
                                                        then
                                                          let uu____4677 =
                                                            let uu____4679 =
                                                              FStar_TypeChecker_Env.get_range
                                                                env
                                                               in
                                                            FStar_Range.string_of_range
                                                              uu____4679
                                                             in
                                                          let uu____4680 =
                                                            FStar_TypeChecker_Rel.guard_to_string
                                                              env guard
                                                             in
                                                          FStar_Util.print2
                                                            "///////////////////////////////EndBind at %s/////////////////////\nguard = %s\n"
                                                            uu____4677
                                                            uu____4680
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
  fun env  ->
    fun m  ->
      fun ct1  ->
        fun b  ->
          fun ct2  ->
            fun flags  ->
              fun r1  ->
                let uu____4729 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____4755 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____4755 with
                  | (a,kwp) ->
                      let uu____4786 = destruct_wp_comp ct1  in
                      let uu____4793 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____4786, uu____4793)
                   in
                match uu____4729 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____4846 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____4846]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____4866 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____4866]
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
                           (FStar_Const.Const_range r1)) r1
                       in
                    let wp_args =
                      let uu____4913 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____4922 =
                        let uu____4933 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____4942 =
                          let uu____4953 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____4962 =
                            let uu____4973 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____4982 =
                              let uu____4993 =
                                let uu____5002 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____5002  in
                              [uu____4993]  in
                            uu____4973 :: uu____4982  in
                          uu____4953 :: uu____4962  in
                        uu____4933 :: uu____4942  in
                      uu____4913 :: uu____4922  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____5053 =
                        FStar_TypeChecker_Env.inst_effect_fun_with
                          [u_t1; u_t2] env md bind_wp
                         in
                      FStar_Syntax_Syntax.mk_Tm_app uu____5053 wp_args
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
              let uu____5101 =
                let uu____5106 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
                let uu____5107 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
                (uu____5106, uu____5107)  in
              match uu____5101 with
              | (ct1,ct2) ->
                  let uu____5114 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name
                     in
                  (match uu____5114 with
                   | FStar_Pervasives_Native.Some (p,f_bind) ->
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None  ->
                       let uu____5165 = lift_comps env c1 c2 b true  in
                       (match uu____5165 with
                        | (m,c11,c21,g_lift) ->
                            let uu____5183 =
                              let uu____5188 =
                                FStar_Syntax_Util.comp_to_comp_typ c11  in
                              let uu____5189 =
                                FStar_Syntax_Util.comp_to_comp_typ c21  in
                              (uu____5188, uu____5189)  in
                            (match uu____5183 with
                             | (ct11,ct21) ->
                                 let uu____5196 =
                                   let uu____5201 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m
                                      in
                                   if uu____5201
                                   then
                                     let bind_t =
                                       let uu____5209 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env)
                                          in
                                       FStar_All.pipe_right uu____5209
                                         FStar_Syntax_Util.get_bind_vc_combinator
                                        in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu____5212 =
                                        mk_wp_bind env m ct11 b ct21 flags r1
                                         in
                                      (uu____5212,
                                        FStar_TypeChecker_Env.trivial_guard))
                                    in
                                 (match uu____5196 with
                                  | (c,g_bind) ->
                                      let uu____5219 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind
                                         in
                                      (c, uu____5219)))))
  
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
            let uu____5255 =
              let uu____5256 =
                let uu____5267 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____5267]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____5256;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____5255  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____5312 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_5318  ->
              match uu___1_5318 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5321 -> false))
       in
    if uu____5312
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_5333  ->
              match uu___2_5333 with
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
        let uu____5361 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5361
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____5372 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____5372  in
           let pure_assume_wp1 =
             let uu____5375 =
               let uu____5376 =
                 FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
               [uu____5376]  in
             let uu____5409 = FStar_TypeChecker_Env.get_range env  in
             FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____5375
               uu____5409
              in
           let uu____5410 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____5410)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5438 =
          let uu____5439 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5439 with
          | (c,g_c) ->
              let uu____5450 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5450
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5464 = weaken_comp env c f1  in
                     (match uu____5464 with
                      | (c1,g_w) ->
                          let uu____5475 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____5475)))
           in
        let uu____5476 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5476 weaken
  
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
                 let uu____5533 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____5533  in
               let pure_assert_wp1 =
                 let uu____5536 =
                   let uu____5537 =
                     let uu____5546 = label_opt env reason r f  in
                     FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                       uu____5546
                      in
                   [uu____5537]  in
                 FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____5536 r
                  in
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
            let uu____5616 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____5616
            then (lc, g0)
            else
              (let flags =
                 let uu____5628 =
                   let uu____5636 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____5636
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5628 with
                 | (maybe_trivial_post,flags) ->
                     let uu____5666 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_5674  ->
                               match uu___3_5674 with
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
                               | uu____5677 -> []))
                        in
                     FStar_List.append flags uu____5666
                  in
               let strengthen uu____5687 =
                 let uu____5688 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____5688 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____5707 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____5707 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____5714 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____5714
                              then
                                let uu____5718 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____5720 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____5718 uu____5720
                              else ());
                             (let uu____5725 =
                                strengthen_comp env reason c f flags  in
                              match uu____5725 with
                              | (c1,g_s) ->
                                  let uu____5736 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____5736))))
                  in
               let uu____5737 =
                 let uu____5738 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____5738
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____5737,
                 (let uu___677_5740 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred_to_tac =
                      (uu___677_5740.FStar_TypeChecker_Common.deferred_to_tac);
                    FStar_TypeChecker_Common.deferred =
                      (uu___677_5740.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___677_5740.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___677_5740.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_5749  ->
            match uu___4_5749 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____5753 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____5782 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____5782
          then e
          else
            (let uu____5789 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____5792 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____5792)
                in
             if uu____5789
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
                | uu____5862 -> false  in
              if is_unit
              then
                let uu____5869 =
                  let uu____5871 =
                    let uu____5872 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____5872
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____5871
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____5869
                 then
                   let uu____5881 = FStar_Syntax_Subst.open_term_bv b phi  in
                   match uu____5881 with
                   | (b1,phi1) ->
                       let phi2 =
                         FStar_Syntax_Subst.subst
                           [FStar_Syntax_Syntax.NT
                              (b1, FStar_Syntax_Syntax.unit_const)] phi1
                          in
                       weaken_comp env c phi2
                 else
                   (let uu____5897 = close_wp_comp env [x] c  in
                    (uu____5897, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____5900 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
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
          fun uu____5928  ->
            match uu____5928 with
            | (b,lc2) ->
                let debug f =
                  let uu____5948 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____5948 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____5961 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____5961
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____5971 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____5971
                       then
                         let uu____5976 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____5976
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5983 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____5983
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5992 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____5992
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____5999 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____5999
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____6015 =
                  let uu____6016 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____6016
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____6024 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____6024, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____6027 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____6027 with
                     | (c1,g_c1) ->
                         let uu____6038 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____6038 with
                          | (c2,g_c2) ->
                              let trivial_guard =
                                let uu____6050 =
                                  match b with
                                  | FStar_Pervasives_Native.Some x ->
                                      let b1 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      let uu____6053 =
                                        FStar_Syntax_Syntax.is_null_binder b1
                                         in
                                      if uu____6053
                                      then g_c2
                                      else
                                        FStar_TypeChecker_Env.close_guard env
                                          [b1] g_c2
                                  | FStar_Pervasives_Native.None  -> g_c2  in
                                FStar_TypeChecker_Env.conj_guard g_c1
                                  uu____6050
                                 in
                              (debug
                                 (fun uu____6079  ->
                                    let uu____6080 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____6082 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____6087 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____6080 uu____6082 uu____6087);
                               (let aux uu____6105 =
                                  let uu____6106 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____6106
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____6137
                                        ->
                                        let uu____6138 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____6138
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____6170 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____6170
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____6217 =
                                  let aux_with_trivial_guard uu____6247 =
                                    let uu____6248 = aux ()  in
                                    match uu____6248 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c, trivial_guard, reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____6306 =
                                    let uu____6308 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____6308  in
                                  if uu____6306
                                  then
                                    let uu____6324 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____6324
                                     then
                                       FStar_Util.Inl
                                         (c2, trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____6351 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____6351))
                                  else
                                    (let uu____6368 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____6368
                                     then
                                       let close_with_type_of_x x c =
                                         let x1 =
                                           let uu___780_6399 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___780_6399.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___780_6399.FStar_Syntax_Syntax.index);
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
                                           let uu____6430 =
                                             let uu____6435 =
                                               FStar_All.pipe_right c2
                                                 (FStar_Syntax_Subst.subst_comp
                                                    [FStar_Syntax_Syntax.NT
                                                       (x, e)])
                                                in
                                             FStar_All.pipe_right uu____6435
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6430 with
                                            | (c21,g_close) ->
                                                let uu____6456 =
                                                  let uu____6464 =
                                                    let uu____6465 =
                                                      let uu____6468 =
                                                        let uu____6471 =
                                                          FStar_TypeChecker_Env.map_guard
                                                            g_c2
                                                            (FStar_Syntax_Subst.subst
                                                               [FStar_Syntax_Syntax.NT
                                                                  (x, e)])
                                                           in
                                                        [uu____6471; g_close]
                                                         in
                                                      g_c1 :: uu____6468  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6465
                                                     in
                                                  (c21, uu____6464, "c1 Tot")
                                                   in
                                                FStar_Util.Inl uu____6456)
                                       | (uu____6484,FStar_Pervasives_Native.Some
                                          x) ->
                                           let uu____6496 =
                                             FStar_All.pipe_right c2
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6496 with
                                            | (c21,g_close) ->
                                                let uu____6519 =
                                                  let uu____6527 =
                                                    let uu____6528 =
                                                      let uu____6531 =
                                                        let uu____6534 =
                                                          let uu____6535 =
                                                            let uu____6536 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____6536]  in
                                                          FStar_TypeChecker_Env.close_guard
                                                            env uu____6535
                                                            g_c2
                                                           in
                                                        [uu____6534; g_close]
                                                         in
                                                      g_c1 :: uu____6531  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6528
                                                     in
                                                  (c21, uu____6527,
                                                    "c1 Tot only close")
                                                   in
                                                FStar_Util.Inl uu____6519)
                                       | (uu____6565,uu____6566) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____6581 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____6581
                                        then
                                          let uu____6596 =
                                            let uu____6604 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____6604, trivial_guard,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____6596
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____6617 = try_simplify ()  in
                                match uu____6617 with
                                | FStar_Util.Inl (c,g,reason) ->
                                    (debug
                                       (fun uu____6652  ->
                                          let uu____6653 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____6653);
                                     (c, g))
                                | FStar_Util.Inr reason ->
                                    (debug
                                       (fun uu____6669  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 g =
                                        let uu____6700 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____6700 with
                                        | (c,g_bind) ->
                                            let uu____6711 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g g_bind
                                               in
                                            (c, uu____6711)
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
                                        let uu____6738 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____6738 with
                                        | (m,uu____6750,lift2) ->
                                            let uu____6752 =
                                              lift_comp env c22 lift2  in
                                            (match uu____6752 with
                                             | (c23,g2) ->
                                                 let uu____6763 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____6763 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let trivial =
                                                        let uu____6779 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____6779
                                                          FStar_Util.must
                                                         in
                                                      let vc1 =
                                                        let uu____6787 =
                                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                                            [u1] env
                                                            md_pure_or_ghost
                                                            trivial
                                                           in
                                                        let uu____6788 =
                                                          let uu____6789 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              t1
                                                             in
                                                          let uu____6798 =
                                                            let uu____6809 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                wp1
                                                               in
                                                            [uu____6809]  in
                                                          uu____6789 ::
                                                            uu____6798
                                                           in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____6787
                                                          uu____6788 r1
                                                         in
                                                      let uu____6842 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____6842 with
                                                       | (c,g_s) ->
                                                           let uu____6857 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____6857))))
                                         in
                                      let uu____6858 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____6874 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____6874, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____6858 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____6890 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____6890
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____6899 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____6899
                                             then
                                               (debug
                                                  (fun uu____6913  ->
                                                     let uu____6914 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____6916 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____6914 uu____6916);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 let g =
                                                   let uu____6923 =
                                                     FStar_TypeChecker_Env.map_guard
                                                       g_c2
                                                       (FStar_Syntax_Subst.subst
                                                          [FStar_Syntax_Syntax.NT
                                                             (x, e1)])
                                                      in
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 uu____6923
                                                    in
                                                 mk_bind1 c1 b c21 g))
                                             else
                                               (let uu____6928 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____6931 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____6931)
                                                   in
                                                if uu____6928
                                                then
                                                  let e1' =
                                                    let uu____6956 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____6956
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug
                                                     (fun uu____6968  ->
                                                        let uu____6969 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____6971 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____6969
                                                          uu____6971);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug
                                                     (fun uu____6986  ->
                                                        let uu____6987 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____6989 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____6987
                                                          uu____6989);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____6996 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____6996
                                                       in
                                                    let uu____6997 =
                                                      let uu____7002 =
                                                        let uu____7003 =
                                                          let uu____7004 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____7004]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____7003
                                                         in
                                                      weaken_comp uu____7002
                                                        c21 x_eq_e
                                                       in
                                                    match uu____6997 with
                                                    | (c22,g_w) ->
                                                        let g =
                                                          let uu____7030 =
                                                            let uu____7031 =
                                                              let uu____7032
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x
                                                                 in
                                                              [uu____7032]
                                                               in
                                                            let uu____7051 =
                                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                                g_c2 x_eq_e
                                                               in
                                                            FStar_TypeChecker_Env.close_guard
                                                              env uu____7031
                                                              uu____7051
                                                             in
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g_c1 uu____7030
                                                           in
                                                        let uu____7052 =
                                                          mk_bind1 c1 b c22 g
                                                           in
                                                        (match uu____7052
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____7063 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____7063))))))
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
      | uu____7080 -> g2
  
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
            (let uu____7104 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____7104)
           in
        let flags =
          if should_return1
          then
            let uu____7112 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____7112
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine uu____7130 =
          let uu____7131 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____7131 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____7144 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____7144
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____7152 =
                  let uu____7154 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____7154  in
                (if uu____7152
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___905_7163 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___905_7163.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___905_7163.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___905_7163.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____7164 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____7164, g_c)
                 else
                   (let uu____7167 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____7167, g_c)))
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
                   let uu____7178 =
                     let uu____7179 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____7179
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____7178
                    in
                 let eq = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret
                     (FStar_TypeChecker_Common.NonTrivial eq)
                    in
                 let uu____7182 =
                   let uu____7187 =
                     let uu____7188 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____7188
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____7187  in
                 match uu____7182 with
                 | (bind_c,g_bind) ->
                     let uu____7197 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____7198 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____7197, uu____7198))
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
            fun uu____7234  ->
              match uu____7234 with
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
                    let uu____7246 =
                      ((let uu____7250 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____7250) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____7246
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____7268 =
        let uu____7269 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____7269  in
      FStar_Syntax_Syntax.fvar uu____7268 FStar_Syntax_Syntax.delta_constant
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
                  let conjunction_name =
                    let uu____7321 =
                      FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname
                       in
                    FStar_Util.format1 "%s.conjunction" uu____7321  in
                  let uu____7324 =
                    let uu____7329 =
                      let uu____7330 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____7330 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7329 [u_a]
                     in
                  match uu____7324 with
                  | (uu____7341,conjunction) ->
                      let uu____7343 =
                        let uu____7352 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____7367 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____7352, uu____7367)  in
                      (match uu____7343 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____7413 =
                               let uu____7415 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format3
                                 "conjunction %s (%s) does not have proper shape (reason:%s)"
                                 uu____7415 conjunction_name s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7413)
                              in
                           let uu____7419 =
                             let uu____7464 =
                               let uu____7465 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____7465.FStar_Syntax_Syntax.n  in
                             match uu____7464 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____7514) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____7546 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____7546 with
                                  | (a_b::bs1,body1) ->
                                      let uu____7618 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____7618 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____7766 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____7766)))
                             | uu____7799 ->
                                 let uu____7800 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____7800 r
                              in
                           (match uu____7419 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____7925 =
                                  let uu____7932 =
                                    let uu____7933 =
                                      let uu____7934 =
                                        let uu____7941 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____7941, a)  in
                                      FStar_Syntax_Syntax.NT uu____7934  in
                                    [uu____7933]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____7932
                                    (fun b  ->
                                       let uu____7957 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____7959 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____7961 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____7957 uu____7959 uu____7961) r
                                   in
                                (match uu____7925 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____7999 =
                                                let uu____8006 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____8006, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____7999) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____8045 =
                                           let uu____8046 =
                                             let uu____8049 =
                                               let uu____8050 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8050.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8049
                                              in
                                           uu____8046.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8045 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8061,uu____8062::is) ->
                                             let uu____8104 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8104
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8137 ->
                                             let uu____8138 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8138 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____8154 =
                                                  FStar_TypeChecker_Rel.layered_effect_teq
                                                    env i1 f_i
                                                    (FStar_Pervasives_Native.Some
                                                       conjunction_name)
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8154)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____8160 =
                                           let uu____8161 =
                                             let uu____8164 =
                                               let uu____8165 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8165.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8164
                                              in
                                           uu____8161.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8160 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8176,uu____8177::is) ->
                                             let uu____8219 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8219
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8252 ->
                                             let uu____8253 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8253 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____8269 =
                                                  FStar_TypeChecker_Rel.layered_effect_teq
                                                    env i2 g_i
                                                    (FStar_Pervasives_Native.Some
                                                       conjunction_name)
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8269)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____8275 =
                                         let uu____8276 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____8276.FStar_Syntax_Syntax.n  in
                                       match uu____8275 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8281,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8336 ->
                                           let uu____8337 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____8337 r
                                        in
                                     let uu____8346 =
                                       let uu____8347 =
                                         let uu____8348 =
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
                                             uu____8348;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____8347
                                        in
                                     let uu____8371 =
                                       let uu____8372 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8372 g_guard
                                        in
                                     (uu____8346, uu____8371))))
  
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
                fun uu____8417  ->
                  let if_then_else =
                    let uu____8423 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____8423 FStar_Util.must  in
                  let uu____8430 = destruct_wp_comp ct1  in
                  match uu____8430 with
                  | (uu____8441,uu____8442,wp_t) ->
                      let uu____8444 = destruct_wp_comp ct2  in
                      (match uu____8444 with
                       | (uu____8455,uu____8456,wp_e) ->
                           let wp =
                             let uu____8459 =
                               FStar_TypeChecker_Env.inst_effect_fun_with
                                 [u_a] env ed if_then_else
                                in
                             let uu____8460 =
                               let uu____8461 = FStar_Syntax_Syntax.as_arg a
                                  in
                               let uu____8470 =
                                 let uu____8481 =
                                   FStar_Syntax_Syntax.as_arg p  in
                                 let uu____8490 =
                                   let uu____8501 =
                                     FStar_Syntax_Syntax.as_arg wp_t  in
                                   let uu____8510 =
                                     let uu____8521 =
                                       FStar_Syntax_Syntax.as_arg wp_e  in
                                     [uu____8521]  in
                                   uu____8501 :: uu____8510  in
                                 uu____8481 :: uu____8490  in
                               uu____8461 :: uu____8470  in
                             let uu____8570 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Syntax.mk_Tm_app uu____8459
                               uu____8460 uu____8570
                              in
                           let uu____8571 = mk_comp ed u_a a wp []  in
                           (uu____8571, FStar_TypeChecker_Env.trivial_guard))
  
let (comp_pure_wp_false :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun u  ->
      fun t  ->
        let post_k =
          let uu____8591 =
            let uu____8600 = FStar_Syntax_Syntax.null_binder t  in
            [uu____8600]  in
          let uu____8619 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
          FStar_Syntax_Util.arrow uu____8591 uu____8619  in
        let kwp =
          let uu____8625 =
            let uu____8634 = FStar_Syntax_Syntax.null_binder post_k  in
            [uu____8634]  in
          let uu____8653 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
          FStar_Syntax_Util.arrow uu____8625 uu____8653  in
        let post =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k  in
        let wp =
          let uu____8660 =
            let uu____8661 = FStar_Syntax_Syntax.mk_binder post  in
            [uu____8661]  in
          let uu____8680 = fvar_const env FStar_Parser_Const.false_lid  in
          FStar_Syntax_Util.abs uu____8660 uu____8680
            (FStar_Pervasives_Native.Some
               (FStar_Syntax_Util.mk_residual_comp
                  FStar_Parser_Const.effect_Tot_lid
                  FStar_Pervasives_Native.None [FStar_Syntax_Syntax.TOTAL]))
           in
        let md =
          FStar_TypeChecker_Env.get_effect_decl env
            FStar_Parser_Const.effect_PURE_lid
           in
        mk_comp md u t wp []
  
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
            let uu____8739 =
              let uu____8740 =
                FStar_All.pipe_right scrutinee FStar_Syntax_Syntax.mk_binder
                 in
              [uu____8740]  in
            FStar_TypeChecker_Env.push_binders env0 uu____8739  in
          let eff =
            FStar_List.fold_left
              (fun eff  ->
                 fun uu____8787  ->
                   match uu____8787 with
                   | (uu____8801,eff_label,uu____8803,uu____8804) ->
                       join_effects env eff eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases
             in
          let uu____8817 =
            let uu____8825 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu____8863  ->
                      match uu____8863 with
                      | (uu____8878,uu____8879,flags,uu____8881) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___5_8898  ->
                                  match uu___5_8898 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                      true
                                  | uu____8901 -> false))))
               in
            if uu____8825
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, [])  in
          match uu____8817 with
          | (should_not_inline_whole_match,bind_cases_flags) ->
              let bind_cases uu____8938 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                   in
                let uu____8940 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                   in
                if uu____8940
                then
                  let uu____8947 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                     in
                  (uu____8947, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let maybe_return eff_label_then cthen =
                     let uu____8968 =
                       should_not_inline_whole_match ||
                         (let uu____8971 = is_pure_or_ghost_effect env eff
                             in
                          Prims.op_Negation uu____8971)
                        in
                     if uu____8968 then cthen true else cthen false  in
                   let uu____8978 =
                     let uu____8989 =
                       let uu____9002 =
                         let uu____9007 =
                           let uu____9018 =
                             FStar_All.pipe_right lcases
                               (FStar_List.map
                                  (fun uu____9068  ->
                                     match uu____9068 with
                                     | (g,uu____9087,uu____9088,uu____9089)
                                         -> g))
                              in
                           FStar_All.pipe_right uu____9018
                             (FStar_List.fold_left
                                (fun uu____9137  ->
                                   fun g  ->
                                     match uu____9137 with
                                     | (conds,acc) ->
                                         let cond =
                                           let uu____9178 =
                                             FStar_Syntax_Util.mk_neg g  in
                                           FStar_Syntax_Util.mk_conj acc
                                             uu____9178
                                            in
                                         ((FStar_List.append conds [cond]),
                                           cond))
                                ([FStar_Syntax_Util.t_true],
                                  FStar_Syntax_Util.t_true))
                            in
                         FStar_All.pipe_right uu____9007
                           FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____9002
                         (fun l  ->
                            FStar_List.splitAt
                              ((FStar_List.length l) - Prims.int_one) l)
                        in
                     FStar_All.pipe_right uu____8989
                       (fun uu____9276  ->
                          match uu____9276 with
                          | (l1,l2) ->
                              let uu____9317 = FStar_List.hd l2  in
                              (l1, uu____9317))
                      in
                   match uu____8978 with
                   | (neg_branch_conds,exhaustiveness_branch_cond) ->
                       let uu____9346 =
                         match lcases with
                         | [] ->
                             let uu____9377 =
                               comp_pure_wp_false env u_res_t res_t  in
                             (FStar_Pervasives_Native.None, uu____9377,
                               FStar_TypeChecker_Env.trivial_guard)
                         | uu____9380 ->
                             let uu____9397 =
                               let uu____9430 =
                                 let uu____9441 =
                                   FStar_All.pipe_right neg_branch_conds
                                     (FStar_List.splitAt
                                        ((FStar_List.length lcases) -
                                           Prims.int_one))
                                    in
                                 FStar_All.pipe_right uu____9441
                                   (fun uu____9513  ->
                                      match uu____9513 with
                                      | (l1,l2) ->
                                          let uu____9554 = FStar_List.hd l2
                                             in
                                          (l1, uu____9554))
                                  in
                               match uu____9430 with
                               | (neg_branch_conds1,neg_last) ->
                                   let uu____9611 =
                                     let uu____9650 =
                                       FStar_All.pipe_right lcases
                                         (FStar_List.splitAt
                                            ((FStar_List.length lcases) -
                                               Prims.int_one))
                                        in
                                     FStar_All.pipe_right uu____9650
                                       (fun uu____9862  ->
                                          match uu____9862 with
                                          | (l1,l2) ->
                                              let uu____10013 =
                                                FStar_List.hd l2  in
                                              (l1, uu____10013))
                                      in
                                   (match uu____9611 with
                                    | (lcases1,(g_last,eff_last,uu____10115,c_last))
                                        ->
                                        let uu____10185 =
                                          let lc =
                                            maybe_return eff_last c_last  in
                                          let uu____10191 =
                                            FStar_TypeChecker_Common.lcomp_comp
                                              lc
                                             in
                                          match uu____10191 with
                                          | (c,g) ->
                                              let uu____10202 =
                                                let uu____10203 =
                                                  FStar_Syntax_Util.mk_conj
                                                    g_last neg_last
                                                   in
                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                  g uu____10203
                                                 in
                                              (c, uu____10202)
                                           in
                                        (match uu____10185 with
                                         | (c,g) ->
                                             let uu____10238 =
                                               let uu____10239 =
                                                 FStar_All.pipe_right
                                                   eff_last
                                                   (FStar_TypeChecker_Env.norm_eff_name
                                                      env)
                                                  in
                                               FStar_All.pipe_right
                                                 uu____10239
                                                 (FStar_TypeChecker_Env.get_effect_decl
                                                    env)
                                                in
                                             (lcases1, neg_branch_conds1,
                                               uu____10238, c, g)))
                                in
                             (match uu____9397 with
                              | (lcases1,neg_branch_conds1,md,comp,g_comp) ->
                                  FStar_List.fold_right2
                                    (fun uu____10371  ->
                                       fun neg_cond  ->
                                         fun uu____10373  ->
                                           match (uu____10371, uu____10373)
                                           with
                                           | ((g,eff_label,uu____10433,cthen),
                                              (uu____10435,celse,g_comp1)) ->
                                               let uu____10482 =
                                                 let uu____10487 =
                                                   maybe_return eff_label
                                                     cthen
                                                    in
                                                 FStar_TypeChecker_Common.lcomp_comp
                                                   uu____10487
                                                  in
                                               (match uu____10482 with
                                                | (cthen1,g_then) ->
                                                    let uu____10498 =
                                                      let uu____10509 =
                                                        lift_comps_sep_guards
                                                          env cthen1 celse
                                                          FStar_Pervasives_Native.None
                                                          false
                                                         in
                                                      match uu____10509 with
                                                      | (m,cthen2,celse1,g_lift_then,g_lift_else)
                                                          ->
                                                          let md1 =
                                                            FStar_TypeChecker_Env.get_effect_decl
                                                              env m
                                                             in
                                                          let uu____10537 =
                                                            FStar_All.pipe_right
                                                              cthen2
                                                              FStar_Syntax_Util.comp_to_comp_typ
                                                             in
                                                          let uu____10538 =
                                                            FStar_All.pipe_right
                                                              celse1
                                                              FStar_Syntax_Util.comp_to_comp_typ
                                                             in
                                                          (md1, uu____10537,
                                                            uu____10538,
                                                            g_lift_then,
                                                            g_lift_else)
                                                       in
                                                    (match uu____10498 with
                                                     | (md1,ct_then,ct_else,g_lift_then,g_lift_else)
                                                         ->
                                                         let fn =
                                                           let uu____10589 =
                                                             FStar_All.pipe_right
                                                               md1
                                                               FStar_Syntax_Util.is_layered
                                                              in
                                                           if uu____10589
                                                           then
                                                             mk_layered_conjunction
                                                           else
                                                             mk_non_layered_conjunction
                                                            in
                                                         let uu____10623 =
                                                           let uu____10628 =
                                                             FStar_TypeChecker_Env.get_range
                                                               env
                                                              in
                                                           fn env md1 u_res_t
                                                             res_t g ct_then
                                                             ct_else
                                                             uu____10628
                                                            in
                                                         (match uu____10623
                                                          with
                                                          | (c,g_conjunction)
                                                              ->
                                                              let g_then1 =
                                                                let uu____10640
                                                                  =
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_then
                                                                    g_lift_then
                                                                   in
                                                                let uu____10641
                                                                  =
                                                                  FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    g
                                                                   in
                                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                                  uu____10640
                                                                  uu____10641
                                                                 in
                                                              let g_else =
                                                                let uu____10643
                                                                  =
                                                                  let uu____10644
                                                                    =
                                                                    FStar_Syntax_Util.mk_neg
                                                                    g  in
                                                                  FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    uu____10644
                                                                   in
                                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                                  g_lift_else
                                                                  uu____10643
                                                                 in
                                                              let uu____10647
                                                                =
                                                                FStar_TypeChecker_Env.conj_guards
                                                                  [g_comp1;
                                                                  g_then1;
                                                                  g_else;
                                                                  g_conjunction]
                                                                 in
                                                              ((FStar_Pervasives_Native.Some
                                                                  md1), c,
                                                                uu____10647)))))
                                    lcases1 neg_branch_conds1
                                    ((FStar_Pervasives_Native.Some md), comp,
                                      g_comp))
                          in
                       (match uu____9346 with
                        | (md,comp,g_comp) ->
                            let uu____10663 =
                              let uu____10668 =
                                let check =
                                  FStar_Syntax_Util.mk_imp
                                    exhaustiveness_branch_cond
                                    FStar_Syntax_Util.t_false
                                   in
                                let check1 =
                                  let uu____10675 =
                                    FStar_TypeChecker_Env.get_range env  in
                                  label
                                    FStar_TypeChecker_Err.exhaustiveness_check
                                    uu____10675 check
                                   in
                                strengthen_comp env
                                  FStar_Pervasives_Native.None comp check1
                                  bind_cases_flags
                                 in
                              match uu____10668 with
                              | (c,g) ->
                                  let uu____10686 =
                                    FStar_TypeChecker_Env.conj_guard g_comp g
                                     in
                                  (c, uu____10686)
                               in
                            (match uu____10663 with
                             | (comp1,g_comp1) ->
                                 let g_comp2 =
                                   let uu____10694 =
                                     let uu____10695 =
                                       FStar_All.pipe_right scrutinee
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     [uu____10695]  in
                                   FStar_TypeChecker_Env.close_guard env0
                                     uu____10694 g_comp1
                                    in
                                 (match lcases with
                                  | [] -> (comp1, g_comp2)
                                  | uu____10738::[] -> (comp1, g_comp2)
                                  | uu____10781 ->
                                      let uu____10798 =
                                        let uu____10800 =
                                          FStar_All.pipe_right md
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____10800
                                          FStar_Syntax_Util.is_layered
                                         in
                                      if uu____10798
                                      then (comp1, g_comp2)
                                      else
                                        (let comp2 =
                                           FStar_TypeChecker_Env.comp_to_comp_typ
                                             env comp1
                                            in
                                         let md1 =
                                           FStar_TypeChecker_Env.get_effect_decl
                                             env
                                             comp2.FStar_Syntax_Syntax.effect_name
                                            in
                                         let uu____10813 =
                                           destruct_wp_comp comp2  in
                                         match uu____10813 with
                                         | (uu____10824,uu____10825,wp) ->
                                             let ite_wp =
                                               let uu____10828 =
                                                 FStar_All.pipe_right md1
                                                   FStar_Syntax_Util.get_wp_ite_combinator
                                                  in
                                               FStar_All.pipe_right
                                                 uu____10828 FStar_Util.must
                                                in
                                             let wp1 =
                                               let uu____10836 =
                                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                                   [u_res_t] env md1 ite_wp
                                                  in
                                               let uu____10837 =
                                                 let uu____10838 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     res_t
                                                    in
                                                 let uu____10847 =
                                                   let uu____10858 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp
                                                      in
                                                   [uu____10858]  in
                                                 uu____10838 :: uu____10847
                                                  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu____10836 uu____10837
                                                 wp.FStar_Syntax_Syntax.pos
                                                in
                                             let uu____10891 =
                                               mk_comp md1 u_res_t res_t wp1
                                                 bind_cases_flags
                                                in
                                             (uu____10891, g_comp2))))))
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
          let uu____10926 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____10926 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____10942 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____10948 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____10942 uu____10948
              else
                (let uu____10957 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____10963 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____10957 uu____10963)
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
          let uu____10988 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____10988
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____10991 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____10991
        then u_res
        else
          (let is_total =
             let uu____10998 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____10998
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____11009 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____11009 with
              | FStar_Pervasives_Native.None  ->
                  let uu____11012 =
                    let uu____11018 =
                      let uu____11020 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____11020
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____11018)
                     in
                  FStar_Errors.raise_error uu____11012
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
      let uu____11044 = destruct_wp_comp ct  in
      match uu____11044 with
      | (u_t,t,wp) ->
          let vc =
            let uu____11061 =
              let uu____11062 =
                let uu____11063 =
                  FStar_All.pipe_right md
                    FStar_Syntax_Util.get_wp_trivial_combinator
                   in
                FStar_All.pipe_right uu____11063 FStar_Util.must  in
              FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                uu____11062
               in
            let uu____11070 =
              let uu____11071 = FStar_Syntax_Syntax.as_arg t  in
              let uu____11080 =
                let uu____11091 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____11091]  in
              uu____11071 :: uu____11080  in
            let uu____11124 = FStar_TypeChecker_Env.get_range env  in
            FStar_Syntax_Syntax.mk_Tm_app uu____11061 uu____11070 uu____11124
             in
          let uu____11125 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____11125)
  
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
                  let uu____11180 =
                    FStar_TypeChecker_Env.try_lookup_lid env f  in
                  match uu____11180 with
                  | FStar_Pervasives_Native.Some uu____11195 ->
                      ((let uu____11213 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____11213
                        then
                          let uu____11217 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____11217
                        else ());
                       (let coercion =
                          let uu____11223 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____11223
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____11230 =
                            let uu____11231 =
                              let uu____11232 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____11232
                               in
                            (FStar_Pervasives_Native.None, uu____11231)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____11230
                           in
                        let e1 =
                          let uu____11236 =
                            let uu____11237 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____11237]  in
                          FStar_Syntax_Syntax.mk_Tm_app coercion2 uu____11236
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____11271 =
                          let uu____11277 =
                            let uu____11279 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____11279
                             in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____11277)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____11271);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____11298 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____11316 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____11327 -> false 
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
      let uu____11351 = FStar_Syntax_Util.head_and_args t2  in
      match uu____11351 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____11396 =
              let uu____11411 =
                let uu____11412 = FStar_Syntax_Subst.compress h1  in
                uu____11412.FStar_Syntax_Syntax.n  in
              (uu____11411, args)  in
            match uu____11396 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____11459,uu____11460) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____11493) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match
               (uu____11514,branches),uu____11516) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc  ->
                        fun br  ->
                          match acc with
                          | Yes uu____11580 -> Maybe
                          | Maybe  -> Maybe
                          | No  ->
                              let uu____11581 =
                                FStar_Syntax_Subst.open_branch br  in
                              (match uu____11581 with
                               | (uu____11582,uu____11583,br_body) ->
                                   let uu____11601 =
                                     let uu____11602 =
                                       let uu____11607 =
                                         let uu____11608 =
                                           let uu____11611 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names
                                              in
                                           FStar_All.pipe_right uu____11611
                                             FStar_Util.set_elements
                                            in
                                         FStar_All.pipe_right uu____11608
                                           (FStar_TypeChecker_Env.push_bvs
                                              env)
                                          in
                                       check_erased uu____11607  in
                                     FStar_All.pipe_right br_body uu____11602
                                      in
                                   (match uu____11601 with
                                    | No  -> No
                                    | uu____11622 -> Maybe))) No)
            | uu____11623 -> No  in
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
            (((let uu____11675 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____11675) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____11694 =
                 let uu____11695 = FStar_Syntax_Subst.compress t1  in
                 uu____11695.FStar_Syntax_Syntax.n  in
               match uu____11694 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____11700 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____11710 =
                 let uu____11711 = FStar_Syntax_Subst.compress t1  in
                 uu____11711.FStar_Syntax_Syntax.n  in
               match uu____11710 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____11716 -> false  in
             let is_type t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let t2 = FStar_Syntax_Util.unrefine t1  in
               let uu____11727 =
                 let uu____11728 = FStar_Syntax_Subst.compress t2  in
                 uu____11728.FStar_Syntax_Syntax.n  in
               match uu____11727 with
               | FStar_Syntax_Syntax.Tm_type uu____11732 -> true
               | uu____11734 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____11737 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____11737 with
             | (head,args) ->
                 ((let uu____11787 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____11787
                   then
                     let uu____11791 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____11793 = FStar_Syntax_Print.term_to_string e
                        in
                     let uu____11795 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____11797 =
                       FStar_Syntax_Print.term_to_string exp_t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____11791 uu____11793 uu____11795 uu____11797
                   else ());
                  (let mk_erased u t =
                     let uu____11815 =
                       let uu____11818 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____11818 [u]  in
                     let uu____11819 =
                       let uu____11830 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____11830]  in
                     FStar_Syntax_Util.mk_app uu____11815 uu____11819  in
                   let uu____11855 =
                     let uu____11870 =
                       let uu____11871 = FStar_Syntax_Util.un_uinst head  in
                       uu____11871.FStar_Syntax_Syntax.n  in
                     (uu____11870, args)  in
                   match uu____11855 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type exp_t)
                       ->
                       let uu____11909 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____11909 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____11949 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11949 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11989 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11989 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____12029 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____12029 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____12050 ->
                       let uu____12065 =
                         let uu____12070 = check_erased env res_typ  in
                         let uu____12071 = check_erased env exp_t  in
                         (uu____12070, uu____12071)  in
                       (match uu____12065 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____12080 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____12080 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____12091 =
                                   let uu____12096 =
                                     let uu____12097 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____12097]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____12096
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____12091 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____12132 =
                              let uu____12137 =
                                let uu____12138 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____12138]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____12137
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____12132 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____12171 ->
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
        let uu____12206 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____12206 with
        | (hd,args) ->
            let uu____12255 =
              let uu____12270 =
                let uu____12271 = FStar_Syntax_Subst.compress hd  in
                uu____12271.FStar_Syntax_Syntax.n  in
              (uu____12270, args)  in
            (match uu____12255 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____12309 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun uu____12336  ->
                      FStar_Pervasives_Native.Some uu____12336) uu____12309
             | uu____12337 -> FStar_Pervasives_Native.None)
  
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
          (let uu____12390 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____12390
           then
             let uu____12393 = FStar_Syntax_Print.term_to_string e  in
             let uu____12395 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____12397 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____12393 uu____12395 uu____12397
           else ());
          (let use_eq =
             (env.FStar_TypeChecker_Env.use_eq_strict ||
                env.FStar_TypeChecker_Env.use_eq)
               ||
               (let uu____12407 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____12407 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____12432 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____12458 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____12458, false)
             else
               (let uu____12468 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____12468, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____12481) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____12493 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____12493
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1393_12509 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1393_12509.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1393_12509.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1393_12509.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard) ->
               let uu____12516 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____12516 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____12532 =
                      let uu____12533 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____12533 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____12553 =
                            let uu____12555 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____12555 = FStar_Syntax_Util.Equal  in
                          if uu____12553
                          then
                            ((let uu____12562 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____12562
                              then
                                let uu____12566 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____12568 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____12566 uu____12568
                              else ());
                             (let uu____12573 = set_result_typ c  in
                              (uu____12573, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____12580 ->
                                   true
                               | uu____12588 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____12597 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____12597
                                  in
                               let lc1 =
                                 let uu____12599 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____12600 =
                                   let uu____12601 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____12601)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____12599 uu____12600
                                  in
                               ((let uu____12605 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____12605
                                 then
                                   let uu____12609 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____12611 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____12613 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____12615 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____12609 uu____12611 uu____12613
                                     uu____12615
                                 else ());
                                (let uu____12620 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____12620 with
                                 | (c1,g_lc) ->
                                     let uu____12631 = set_result_typ c1  in
                                     let uu____12632 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____12631, uu____12632)))
                             else
                               ((let uu____12636 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____12636
                                 then
                                   let uu____12640 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____12642 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____12640 uu____12642
                                 else ());
                                (let uu____12647 = set_result_typ c  in
                                 (uu____12647, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1430_12651 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred_to_tac =
                          (uu___1430_12651.FStar_TypeChecker_Common.deferred_to_tac);
                        FStar_TypeChecker_Common.deferred =
                          (uu___1430_12651.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1430_12651.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1430_12651.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____12661 =
                      let uu____12662 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____12662
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____12672 =
                           let uu____12673 = FStar_Syntax_Subst.compress f1
                              in
                           uu____12673.FStar_Syntax_Syntax.n  in
                         match uu____12672 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____12680,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____12682;
                                            FStar_Syntax_Syntax.vars =
                                              uu____12683;_},uu____12684)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1446_12710 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1446_12710.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1446_12710.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1446_12710.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____12711 ->
                             let uu____12712 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____12712 with
                              | (c,g_c) ->
                                  ((let uu____12724 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____12724
                                    then
                                      let uu____12728 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____12730 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____12732 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____12734 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____12728 uu____12730 uu____12732
                                        uu____12734
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
                                        let uu____12747 =
                                          let uu____12748 =
                                            FStar_Syntax_Syntax.as_arg xexp
                                             in
                                          [uu____12748]  in
                                        FStar_Syntax_Syntax.mk_Tm_app f1
                                          uu____12747
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____12775 =
                                      let uu____12780 =
                                        FStar_All.pipe_left
                                          (fun uu____12801  ->
                                             FStar_Pervasives_Native.Some
                                               uu____12801)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____12802 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____12803 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____12804 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____12780
                                        uu____12802 e uu____12803 uu____12804
                                       in
                                    match uu____12775 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1464_12812 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1464_12812.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1464_12812.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____12814 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____12814
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____12817 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____12817 with
                                         | (c2,g_lc) ->
                                             ((let uu____12829 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____12829
                                               then
                                                 let uu____12833 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____12833
                                               else ());
                                              (let uu____12838 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____12838))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_12847  ->
                              match uu___6_12847 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____12850 -> []))
                       in
                    let lc1 =
                      let uu____12852 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____12852 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1480_12854 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred_to_tac =
                          (uu___1480_12854.FStar_TypeChecker_Common.deferred_to_tac);
                        FStar_TypeChecker_Common.deferred =
                          (uu___1480_12854.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1480_12854.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1480_12854.FStar_TypeChecker_Common.implicits)
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
        let uu____12890 =
          let uu____12893 =
            let uu____12894 =
              let uu____12903 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_Syntax_Syntax.as_arg uu____12903  in
            [uu____12894]  in
          FStar_Syntax_Syntax.mk_Tm_app ens uu____12893
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____12890  in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____12926 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____12926
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____12945 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____12961 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____12978 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____12978
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____12994)::(ens,uu____12996)::uu____12997 ->
                    let uu____13040 =
                      let uu____13043 = norm req  in
                      FStar_Pervasives_Native.Some uu____13043  in
                    let uu____13044 =
                      let uu____13045 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm uu____13045  in
                    (uu____13040, uu____13044)
                | uu____13048 ->
                    let uu____13059 =
                      let uu____13065 =
                        let uu____13067 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____13067
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____13065)
                       in
                    FStar_Errors.raise_error uu____13059
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____13087)::uu____13088 ->
                    let uu____13115 =
                      let uu____13120 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____13120
                       in
                    (match uu____13115 with
                     | (us_r,uu____13152) ->
                         let uu____13153 =
                           let uu____13158 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____13158
                            in
                         (match uu____13153 with
                          | (us_e,uu____13190) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____13193 =
                                  let uu____13194 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____13194
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____13193
                                  us_r
                                 in
                              let as_ens =
                                let uu____13196 =
                                  let uu____13197 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____13197
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____13196
                                  us_e
                                 in
                              let req =
                                let uu____13199 =
                                  let uu____13200 =
                                    let uu____13211 =
                                      FStar_Syntax_Syntax.as_arg wp  in
                                    [uu____13211]  in
                                  ((ct1.FStar_Syntax_Syntax.result_typ),
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.imp_tag))
                                    :: uu____13200
                                   in
                                FStar_Syntax_Syntax.mk_Tm_app as_req
                                  uu____13199
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____13249 =
                                  let uu____13250 =
                                    let uu____13261 =
                                      FStar_Syntax_Syntax.as_arg wp  in
                                    [uu____13261]  in
                                  ((ct1.FStar_Syntax_Syntax.result_typ),
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.imp_tag))
                                    :: uu____13250
                                   in
                                FStar_Syntax_Syntax.mk_Tm_app as_ens
                                  uu____13249
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____13298 =
                                let uu____13301 = norm req  in
                                FStar_Pervasives_Native.Some uu____13301  in
                              let uu____13302 =
                                let uu____13303 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm uu____13303  in
                              (uu____13298, uu____13302)))
                | uu____13306 -> failwith "Impossible"))
  
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
        (let uu____13345 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____13345
         then
           let uu____13350 = FStar_Syntax_Print.term_to_string tm  in
           let uu____13352 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____13350
             uu____13352
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
              head.FStar_Syntax_Syntax.pos
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
          (let uu____13411 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____13411
           then
             let uu____13416 = FStar_Syntax_Print.term_to_string tm  in
             let uu____13418 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____13416
               uu____13418
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____13429 =
      let uu____13431 =
        let uu____13432 = FStar_Syntax_Subst.compress t  in
        uu____13432.FStar_Syntax_Syntax.n  in
      match uu____13431 with
      | FStar_Syntax_Syntax.Tm_app uu____13436 -> false
      | uu____13454 -> true  in
    if uu____13429
    then t
    else
      (let uu____13459 = FStar_Syntax_Util.head_and_args t  in
       match uu____13459 with
       | (head,args) ->
           let uu____13502 =
             let uu____13504 =
               let uu____13505 = FStar_Syntax_Subst.compress head  in
               uu____13505.FStar_Syntax_Syntax.n  in
             match uu____13504 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____13510 -> false  in
           if uu____13502
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____13542 ->
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
          ((let uu____13589 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____13589
            then
              let uu____13592 = FStar_Syntax_Print.term_to_string e  in
              let uu____13594 = FStar_Syntax_Print.term_to_string t  in
              let uu____13596 =
                let uu____13598 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____13598
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____13592 uu____13594 uu____13596
            else ());
           (let unfolded_arrow_formals t1 =
              let rec aux bs t2 =
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf env t2  in
                let uu____13634 = FStar_Syntax_Util.arrow_formals t3  in
                match uu____13634 with
                | (bs',t4) ->
                    (match bs' with
                     | [] -> bs
                     | bs'1 -> aux (FStar_List.append bs bs'1) t4)
                 in
              aux [] t1  in
            let number_of_implicits t1 =
              let formals = unfolded_arrow_formals t1  in
              let n_implicits =
                let uu____13668 =
                  FStar_All.pipe_right formals
                    (FStar_Util.prefix_until
                       (fun uu____13746  ->
                          match uu____13746 with
                          | (uu____13754,imp) ->
                              (FStar_Option.isNone imp) ||
                                (let uu____13761 =
                                   FStar_Syntax_Util.eq_aqual imp
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Equality)
                                    in
                                 uu____13761 = FStar_Syntax_Util.Equal)))
                   in
                match uu____13668 with
                | FStar_Pervasives_Native.None  -> FStar_List.length formals
                | FStar_Pervasives_Native.Some
                    (implicits,_first_explicit,_rest) ->
                    FStar_List.length implicits
                 in
              n_implicits  in
            let inst_n_binders t1 =
              let uu____13880 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____13880 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____13894 =
                      let uu____13900 =
                        let uu____13902 = FStar_Util.string_of_int n_expected
                           in
                        let uu____13904 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____13906 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____13902 uu____13904 uu____13906
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____13900)
                       in
                    let uu____13910 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____13894 uu____13910
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_13928 =
              match uu___7_13928 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____13971 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____13971 with
                 | (bs1,c1) ->
                     let rec aux subst inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some
                          uu____14102,uu____14089) when
                           uu____14102 = Prims.int_zero ->
                           ([], bs2, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____14135,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____14137))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____14171 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____14171 with
                            | (v,uu____14212,g) ->
                                ((let uu____14227 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____14227
                                  then
                                    let uu____14230 =
                                      FStar_Syntax_Print.term_to_string v  in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____14230
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst
                                     in
                                  let uu____14240 =
                                    aux subst1 (decr_inst inst_n) rest  in
                                  match uu____14240 with
                                  | (args,bs3,subst2,g') ->
                                      let uu____14333 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____14333))))
                       | (uu____14360,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta
                                       tac_or_attr))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort
                              in
                           let meta_t =
                             match tac_or_attr with
                             | FStar_Syntax_Syntax.Arg_qualifier_meta_tac tau
                                 ->
                                 let uu____14399 =
                                   let uu____14406 = FStar_Dyn.mkdyn env  in
                                   (uu____14406, tau)  in
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   uu____14399
                             | FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                 attr ->
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_attr attr
                              in
                           let uu____14412 =
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict
                               (FStar_Pervasives_Native.Some meta_t)
                              in
                           (match uu____14412 with
                            | (v,uu____14453,g) ->
                                ((let uu____14468 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____14468
                                  then
                                    let uu____14471 =
                                      FStar_Syntax_Print.term_to_string v  in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____14471
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst
                                     in
                                  let uu____14481 =
                                    aux subst1 (decr_inst inst_n) rest  in
                                  match uu____14481 with
                                  | (args,bs3,subst2,g') ->
                                      let uu____14574 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____14574))))
                       | (uu____14601,bs3) ->
                           ([], bs3, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____14649 =
                       let uu____14676 = inst_n_binders t1  in
                       aux [] uu____14676 bs1  in
                     (match uu____14649 with
                      | (args,bs2,subst,guard) ->
                          (match (args, bs2) with
                           | ([],uu____14748) -> (e, torig, guard)
                           | (uu____14779,[]) when
                               let uu____14810 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____14810 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____14812 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____14840 ->
                                     FStar_Syntax_Util.arrow bs2 c1
                                  in
                               let t3 = FStar_Syntax_Subst.subst subst t2  in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               (e1, t3, guard))))
            | uu____14851 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs  ->
    let uu____14863 =
      let uu____14867 = FStar_Util.set_elements univs  in
      FStar_All.pipe_right uu____14867
        (FStar_List.map
           (fun u  ->
              let uu____14879 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____14879 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____14863 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____14907 = FStar_Util.set_is_empty x  in
      if uu____14907
      then []
      else
        (let s =
           let uu____14927 =
             let uu____14930 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____14930  in
           FStar_All.pipe_right uu____14927 FStar_Util.set_elements  in
         (let uu____14948 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____14948
          then
            let uu____14953 =
              let uu____14955 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____14955  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____14953
          else ());
         (let r =
            let uu____14964 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____14964  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____15009 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____15009
                     then
                       let uu____15014 =
                         let uu____15016 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____15016
                          in
                       let uu____15020 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____15022 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____15014 uu____15020 uu____15022
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
        let uu____15052 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____15052 FStar_Util.set_elements  in
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
        | ([],uu____15091) -> generalized_univ_names
        | (uu____15098,[]) -> explicit_univ_names
        | uu____15105 ->
            let uu____15114 =
              let uu____15120 =
                let uu____15122 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____15122
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____15120)
               in
            FStar_Errors.raise_error uu____15114 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____15144 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____15144
       then
         let uu____15149 = FStar_Syntax_Print.term_to_string t  in
         let uu____15151 = FStar_Syntax_Print.univ_names_to_string univnames
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____15149 uu____15151
       else ());
      (let univs = FStar_Syntax_Free.univs t  in
       (let uu____15160 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____15160
        then
          let uu____15165 = string_of_univs univs  in
          FStar_Util.print1 "univs to gen : %s\n" uu____15165
        else ());
       (let gen = gen_univs env univs  in
        (let uu____15174 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____15174
         then
           let uu____15179 = FStar_Syntax_Print.term_to_string t  in
           let uu____15181 = FStar_Syntax_Print.univ_names_to_string gen  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____15179 uu____15181
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
        let uu____15265 =
          let uu____15267 =
            FStar_Util.for_all
              (fun uu____15281  ->
                 match uu____15281 with
                 | (uu____15291,uu____15292,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____15267  in
        if uu____15265
        then FStar_Pervasives_Native.None
        else
          (let norm c =
             (let uu____15344 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____15344
              then
                let uu____15347 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____15347
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____15354 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____15354
               then
                 let uu____15357 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____15357
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____15375 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____15375 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____15409 =
             match uu____15409 with
             | (lbname,e,c) ->
                 let c1 = norm c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____15446 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____15446
                   then
                     let uu____15451 =
                       let uu____15453 =
                         let uu____15457 = FStar_Util.set_elements univs  in
                         FStar_All.pipe_right uu____15457
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____15453
                         (FStar_String.concat ", ")
                        in
                     let uu____15513 =
                       let uu____15515 =
                         let uu____15519 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____15519
                           (FStar_List.map
                              (fun u  ->
                                 let uu____15532 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____15534 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____15532
                                   uu____15534))
                          in
                       FStar_All.pipe_right uu____15515
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____15451
                       uu____15513
                   else ());
                  (let univs1 =
                     let uu____15548 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs1  ->
                          fun uv  ->
                            let uu____15560 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs1 uu____15560) univs
                       uu____15548
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____15567 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____15567
                    then
                      let uu____15572 =
                        let uu____15574 =
                          let uu____15578 = FStar_Util.set_elements univs1
                             in
                          FStar_All.pipe_right uu____15578
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____15574
                          (FStar_String.concat ", ")
                         in
                      let uu____15634 =
                        let uu____15636 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____15650 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____15652 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____15650
                                    uu____15652))
                           in
                        FStar_All.pipe_right uu____15636
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____15572 uu____15634
                    else ());
                   (univs1, uvs, (lbname, e, c1))))
              in
           let uu____15673 =
             let uu____15690 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____15690  in
           match uu____15673 with
           | (univs,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____15780 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____15780
                 then ()
                 else
                   (let uu____15785 = lec_hd  in
                    match uu____15785 with
                    | (lb1,uu____15793,uu____15794) ->
                        let uu____15795 = lec2  in
                        (match uu____15795 with
                         | (lb2,uu____15803,uu____15804) ->
                             let msg =
                               let uu____15807 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15809 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____15807 uu____15809
                                in
                             let uu____15812 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____15812))
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
                 let uu____15880 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____15880
                 then ()
                 else
                   (let uu____15885 = lec_hd  in
                    match uu____15885 with
                    | (lb1,uu____15893,uu____15894) ->
                        let uu____15895 = lec2  in
                        (match uu____15895 with
                         | (lb2,uu____15903,uu____15904) ->
                             let msg =
                               let uu____15907 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15909 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____15907 uu____15909
                                in
                             let uu____15912 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____15912))
                  in
               let lecs1 =
                 let uu____15923 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____15976 = univs_and_uvars_of_lec this_lec  in
                        match uu____15976 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____15923 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail rng k =
                   let uu____16086 = lec_hd  in
                   match uu____16086 with
                   | (lbname,e,c) ->
                       let uu____16096 =
                         let uu____16102 =
                           let uu____16104 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____16106 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____16108 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____16104 uu____16106 uu____16108
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____16102)
                          in
                       FStar_Errors.raise_error uu____16096 rng
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____16130 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____16130 with
                         | FStar_Pervasives_Native.Some uu____16139 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____16147 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____16151 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____16151 with
                              | (bs,kres) ->
                                  ((let uu____16171 =
                                      let uu____16172 =
                                        let uu____16175 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____16175
                                         in
                                      uu____16172.FStar_Syntax_Syntax.n  in
                                    match uu____16171 with
                                    | FStar_Syntax_Syntax.Tm_type uu____16176
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____16180 =
                                          let uu____16182 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____16182  in
                                        if uu____16180
                                        then
                                          fail
                                            u.FStar_Syntax_Syntax.ctx_uvar_range
                                            kres
                                        else ()
                                    | uu____16187 ->
                                        fail
                                          u.FStar_Syntax_Syntax.ctx_uvar_range
                                          kres);
                                   (let a =
                                      let uu____16189 =
                                        let uu____16192 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun uu____16195  ->
                                             FStar_Pervasives_Native.Some
                                               uu____16195) uu____16192
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____16189
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____16203 ->
                                          let uu____16204 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____16204
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
                      (fun uu____16307  ->
                         match uu____16307 with
                         | (lbname,e,c) ->
                             let uu____16353 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____16414 ->
                                   let uu____16427 = (e, c)  in
                                   (match uu____16427 with
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
                                                (fun uu____16467  ->
                                                   match uu____16467 with
                                                   | (x,uu____16473) ->
                                                       let uu____16474 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____16474)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____16492 =
                                                let uu____16494 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____16494
                                                 in
                                              if uu____16492
                                              then
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  tm tvar_args
                                                  tm.FStar_Syntax_Syntax.pos
                                              else tm  in
                                            FStar_Syntax_InstFV.inst
                                              instantiate_lbname_with_app e1
                                          else e1  in
                                        let t =
                                          let uu____16503 =
                                            let uu____16504 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____16504.FStar_Syntax_Syntax.n
                                             in
                                          match uu____16503 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____16529 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____16529 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____16540 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____16544 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____16544, gen_tvars))
                                in
                             (match uu____16353 with
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
        (let uu____16691 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____16691
         then
           let uu____16694 =
             let uu____16696 =
               FStar_List.map
                 (fun uu____16711  ->
                    match uu____16711 with
                    | (lb,uu____16720,uu____16721) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____16696 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____16694
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____16747  ->
                match uu____16747 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____16776 = gen env is_rec lecs  in
           match uu____16776 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____16875  ->
                       match uu____16875 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____16937 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____16937
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____16985  ->
                           match uu____16985 with
                           | (l,us,e,c,gvs) ->
                               let uu____17019 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____17021 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____17023 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____17025 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____17027 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____17019 uu____17021 uu____17023
                                 uu____17025 uu____17027))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames  ->
              fun uu____17072  ->
                match uu____17072 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____17116 =
                      check_universe_generalization univnames
                        generalized_univs t
                       in
                    (l, uu____17116, t, c, gvs)) univnames_lecs
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
        let uu____17171 =
          let uu____17175 =
            let uu____17177 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____17177  in
          FStar_Pervasives_Native.Some uu____17175  in
        FStar_Profiling.profile
          (fun uu____17194  -> generalize' env is_rec lecs) uu____17171
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
              let uu____17251 =
                FStar_TypeChecker_Rel.get_teq_predicate env2 t1 t21  in
              match uu____17251 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some f ->
                  let uu____17257 = FStar_TypeChecker_Env.apply_guard f e  in
                  FStar_All.pipe_right uu____17257
                    (fun uu____17260  ->
                       FStar_Pervasives_Native.Some uu____17260)
            else
              if env2.FStar_TypeChecker_Env.use_eq
              then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
              else
                (let uu____17269 =
                   FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                    in
                 match uu____17269 with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some f ->
                     let uu____17275 = FStar_TypeChecker_Env.apply_guard f e
                        in
                     FStar_All.pipe_left
                       (fun uu____17278  ->
                          FStar_Pervasives_Native.Some uu____17278)
                       uu____17275)
             in
          let uu____17279 = maybe_coerce_lc env1 e lc t2  in
          match uu____17279 with
          | (e1,lc1,g_c) ->
              let uu____17295 =
                check env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____17295 with
               | FStar_Pervasives_Native.None  ->
                   let uu____17304 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____17310 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____17304 uu____17310
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____17319 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____17319
                     then
                       let uu____17324 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____17324
                     else ());
                    (let uu____17330 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (e1, lc1, uu____17330))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____17358 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____17358
         then
           let uu____17361 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____17361
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____17375 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____17375 with
         | (c,g_c) ->
             let uu____17387 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____17387
             then
               let uu____17395 =
                 let uu____17397 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____17397  in
               (uu____17395, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____17405 =
                    let uu____17406 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____17406
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____17405
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____17407 = check_trivial_precondition env c1  in
                match uu____17407 with
                | (ct,vc,g_pre) ->
                    ((let uu____17423 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____17423
                      then
                        let uu____17428 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____17428
                      else ());
                     (let uu____17433 =
                        let uu____17435 =
                          let uu____17436 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____17436  in
                        discharge uu____17435  in
                      let uu____17437 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____17433, uu____17437)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head  ->
    fun seen_args  ->
      let short_bin_op f uu___8_17471 =
        match uu___8_17471 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst,uu____17481)::[] -> f fst
        | uu____17506 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____17518 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____17518
          (fun uu____17519  ->
             FStar_TypeChecker_Common.NonTrivial uu____17519)
         in
      let op_or_e e =
        let uu____17530 =
          let uu____17531 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____17531  in
        FStar_All.pipe_right uu____17530
          (fun uu____17534  ->
             FStar_TypeChecker_Common.NonTrivial uu____17534)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun uu____17541  ->
             FStar_TypeChecker_Common.NonTrivial uu____17541)
         in
      let op_or_t t =
        let uu____17552 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____17552
          (fun uu____17555  ->
             FStar_TypeChecker_Common.NonTrivial uu____17555)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun uu____17562  ->
             FStar_TypeChecker_Common.NonTrivial uu____17562)
         in
      let short_op_ite uu___9_17568 =
        match uu___9_17568 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____17578)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____17605)::[] ->
            let uu____17646 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____17646
              (fun uu____17647  ->
                 FStar_TypeChecker_Common.NonTrivial uu____17647)
        | uu____17648 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____17660 =
          let uu____17668 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____17668)  in
        let uu____17676 =
          let uu____17686 =
            let uu____17694 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____17694)  in
          let uu____17702 =
            let uu____17712 =
              let uu____17720 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____17720)  in
            let uu____17728 =
              let uu____17738 =
                let uu____17746 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____17746)  in
              let uu____17754 =
                let uu____17764 =
                  let uu____17772 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____17772)  in
                [uu____17764; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____17738 :: uu____17754  in
            uu____17712 :: uu____17728  in
          uu____17686 :: uu____17702  in
        uu____17660 :: uu____17676  in
      match head.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____17834 =
            FStar_Util.find_map table
              (fun uu____17849  ->
                 match uu____17849 with
                 | (x,mk) ->
                     let uu____17866 = FStar_Ident.lid_equals x lid  in
                     if uu____17866
                     then
                       let uu____17871 = mk seen_args  in
                       FStar_Pervasives_Native.Some uu____17871
                     else FStar_Pervasives_Native.None)
             in
          (match uu____17834 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____17875 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____17883 =
      let uu____17884 = FStar_Syntax_Util.un_uinst l  in
      uu____17884.FStar_Syntax_Syntax.n  in
    match uu____17883 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____17889 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd,uu____17925)::uu____17926 -> FStar_Syntax_Syntax.range_of_bv hd
        | uu____17945 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____17954,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____17955))::uu____17956 -> bs
      | uu____17974 ->
          let uu____17975 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____17975 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____17979 =
                 let uu____17980 = FStar_Syntax_Subst.compress t  in
                 uu____17980.FStar_Syntax_Syntax.n  in
               (match uu____17979 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____17984) ->
                    let uu____18005 =
                      FStar_Util.prefix_until
                        (fun uu___10_18045  ->
                           match uu___10_18045 with
                           | (uu____18053,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____18054)) ->
                               false
                           | uu____18059 -> true) bs'
                       in
                    (match uu____18005 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____18095,uu____18096) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____18168,uu____18169) ->
                         let uu____18242 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____18263  ->
                                   match uu____18263 with
                                   | (x,uu____18272) ->
                                       let uu____18277 =
                                         FStar_Ident.string_of_id
                                           x.FStar_Syntax_Syntax.ppname
                                          in
                                       FStar_Util.starts_with uu____18277 "'"))
                            in
                         if uu____18242
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____18323  ->
                                     match uu____18323 with
                                     | (x,i) ->
                                         let uu____18342 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____18342, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____18353 -> bs))
  
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
            let uu____18382 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____18382
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
  fun env  ->
    fun e  ->
      fun c  ->
        fun t  ->
          let m = FStar_TypeChecker_Env.norm_eff_name env c  in
          let uu____18413 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____18413
          then e
          else
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_meta
                 (e, (FStar_Syntax_Syntax.Meta_monadic (m, t))))
              e.FStar_Syntax_Syntax.pos
  
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
        (let uu____18456 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____18456
         then
           ((let uu____18461 = FStar_Ident.string_of_lid lident  in
             d uu____18461);
            (let uu____18463 = FStar_Ident.string_of_lid lident  in
             let uu____18465 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____18463 uu____18465))
         else ());
        (let fv =
           let uu____18471 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____18471
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
         let uu____18483 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Range.dummyRange
            in
         ((let uu___2107_18485 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2107_18485.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2107_18485.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2107_18485.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2107_18485.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2107_18485.FStar_Syntax_Syntax.sigopts)
           }), uu____18483))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_18503 =
        match uu___11_18503 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____18506 -> false  in
      let reducibility uu___12_18514 =
        match uu___12_18514 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____18521 -> false  in
      let assumption uu___13_18529 =
        match uu___13_18529 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____18533 -> false  in
      let reification uu___14_18541 =
        match uu___14_18541 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____18544 -> true
        | uu____18546 -> false  in
      let inferred uu___15_18554 =
        match uu___15_18554 with
        | FStar_Syntax_Syntax.Discriminator uu____18556 -> true
        | FStar_Syntax_Syntax.Projector uu____18558 -> true
        | FStar_Syntax_Syntax.RecordType uu____18564 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____18574 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____18587 -> false  in
      let has_eq uu___16_18595 =
        match uu___16_18595 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____18599 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____18678 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____18685 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____18718 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____18718))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____18749 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____18749
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
           | FStar_Syntax_Syntax.Sig_bundle uu____18769 ->
               let uu____18778 =
                 let uu____18780 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_18786  ->
                           match uu___17_18786 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____18789 -> false))
                    in
                 Prims.op_Negation uu____18780  in
               if uu____18778
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____18796 -> ()
           | FStar_Syntax_Syntax.Sig_fail uu____18803 -> ()
           | uu____18816 ->
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
      let uu____18830 =
        let uu____18832 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_18838  ->
                  match uu___18_18838 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____18841 -> false))
           in
        FStar_All.pipe_right uu____18832 Prims.op_Negation  in
      if uu____18830
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____18862 =
            let uu____18868 =
              let uu____18870 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____18870 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____18868)  in
          FStar_Errors.raise_error uu____18862 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____18888 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____18896 =
            let uu____18898 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____18898  in
          if uu____18896 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____18909),uu____18910) ->
              ((let uu____18922 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____18922
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____18931 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____18931
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____18942 ->
              ((let uu____18952 =
                  let uu____18954 =
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
                  Prims.op_Negation uu____18954  in
                if uu____18952 then err'1 () else ());
               (let uu____18964 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_18970  ->
                           match uu___19_18970 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____18973 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____18964
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____18979 ->
              let uu____18986 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____18986 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____18994 ->
              let uu____19001 =
                let uu____19003 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____19003  in
              if uu____19001 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____19013 ->
              let uu____19014 =
                let uu____19016 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____19016  in
              if uu____19014 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19026 ->
              let uu____19039 =
                let uu____19041 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____19041  in
              if uu____19039 then err'1 () else ()
          | uu____19051 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____19090 =
          let uu____19091 = FStar_Syntax_Subst.compress t1  in
          uu____19091.FStar_Syntax_Syntax.n  in
        match uu____19090 with
        | FStar_Syntax_Syntax.Tm_arrow uu____19095 ->
            let uu____19110 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____19110 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____19119;
               FStar_Syntax_Syntax.index = uu____19120;
               FStar_Syntax_Syntax.sort = t2;_},uu____19122)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head,uu____19131) -> descend env head
        | FStar_Syntax_Syntax.Tm_uinst (head,uu____19157) -> descend env head
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____19163 -> false
      
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
        (let uu____19173 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____19173
         then
           let uu____19178 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____19178
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
                  let uu____19243 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____19243 r  in
                let uu____19253 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____19253 with
                | (uu____19262,signature) ->
                    let uu____19264 =
                      let uu____19265 = FStar_Syntax_Subst.compress signature
                         in
                      uu____19265.FStar_Syntax_Syntax.n  in
                    (match uu____19264 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____19273) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____19321 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____19337 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____19339 =
                                       FStar_Ident.string_of_lid eff_name  in
                                     let uu____19341 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____19337 uu____19339 uu____19341) r
                                 in
                              (match uu____19321 with
                               | (is,g) ->
                                   let uu____19354 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____19356 =
                                             let uu____19357 =
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
                                                 = uu____19357;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____19356
                                            in
                                         let uu____19376 =
                                           let uu____19377 =
                                             let uu____19392 =
                                               let uu____19401 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   FStar_Syntax_Syntax.t_unit
                                                  in
                                               [uu____19401]  in
                                             (uu____19392, eff_c)  in
                                           FStar_Syntax_Syntax.Tm_arrow
                                             uu____19377
                                            in
                                         FStar_Syntax_Syntax.mk uu____19376 r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____19432 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____19432
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____19441 =
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg (a_tm
                                             :: is)
                                            in
                                         FStar_Syntax_Syntax.mk_Tm_app repr
                                           uu____19441 r
                                      in
                                   (uu____19354, g))
                          | uu____19450 -> fail signature)
                     | uu____19451 -> fail signature)
  
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
            let uu____19482 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____19482
              (fun ed  ->
                 let uu____19490 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____19490 u a_tm)
  
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
              let uu____19526 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____19526 with
              | (uu____19531,sig_tm) ->
                  let fail t =
                    let uu____19539 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____19539 r  in
                  let uu____19545 =
                    let uu____19546 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____19546.FStar_Syntax_Syntax.n  in
                  (match uu____19545 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____19550) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____19573)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____19595 -> fail sig_tm)
                   | uu____19596 -> fail sig_tm)
  
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
          (let uu____19627 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____19627
           then
             let uu____19632 = FStar_Syntax_Print.comp_to_string c  in
             let uu____19634 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____19632 uu____19634
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let lift_name =
             let uu____19643 =
               FStar_Ident.string_of_lid ct.FStar_Syntax_Syntax.effect_name
                in
             let uu____19645 = FStar_Ident.string_of_lid tgt  in
             FStar_Util.format2 "%s ~> %s" uu____19643 uu____19645  in
           let uu____19648 =
             let uu____19659 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____19660 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____19659, (ct.FStar_Syntax_Syntax.result_typ), uu____19660)
              in
           match uu____19648 with
           | (u,a,c_is) ->
               let uu____19708 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____19708 with
                | (uu____19717,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____19728 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____19730 = FStar_Ident.string_of_lid tgt  in
                      let uu____19732 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____19728 uu____19730 s uu____19732
                       in
                    let uu____19735 =
                      let uu____19768 =
                        let uu____19769 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____19769.FStar_Syntax_Syntax.n  in
                      match uu____19768 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____19833 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____19833 with
                           | (a_b::bs1,c2) ->
                               let uu____19893 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               (a_b, uu____19893, c2))
                      | uu____19981 ->
                          let uu____19982 =
                            let uu____19988 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____19988)
                             in
                          FStar_Errors.raise_error uu____19982 r
                       in
                    (match uu____19735 with
                     | (a_b,(rest_bs,f_b::[]),lift_c) ->
                         let uu____20106 =
                           let uu____20113 =
                             let uu____20114 =
                               let uu____20115 =
                                 let uu____20122 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____20122, a)  in
                               FStar_Syntax_Syntax.NT uu____20115  in
                             [uu____20114]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____20113
                             (fun b  ->
                                let uu____20139 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____20141 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____20143 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____20145 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____20139 uu____20141 uu____20143
                                  uu____20145) r
                            in
                         (match uu____20106 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____20159 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____20159
                                then
                                  let uu____20164 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____20173 =
                                             let uu____20175 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____20175
                                              in
                                           Prims.op_Hat s uu____20173) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____20164
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____20206 =
                                           let uu____20213 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____20213, t)  in
                                         FStar_Syntax_Syntax.NT uu____20206)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____20232 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____20232
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____20238 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
                                    effect_args_from_repr f_sort uu____20238
                                      r
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____20247 =
                                             FStar_TypeChecker_Rel.layered_effect_teq
                                               env i1 i2
                                               (FStar_Pervasives_Native.Some
                                                  lift_name)
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____20247)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let lift_ct =
                                  let uu____20250 =
                                    FStar_All.pipe_right lift_c
                                      (FStar_Syntax_Subst.subst_comp substs)
                                     in
                                  FStar_All.pipe_right uu____20250
                                    FStar_Syntax_Util.comp_to_comp_typ
                                   in
                                let is =
                                  let uu____20254 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____20254 r
                                   in
                                let fml =
                                  let uu____20259 =
                                    let uu____20264 =
                                      FStar_List.hd
                                        lift_ct.FStar_Syntax_Syntax.comp_univs
                                       in
                                    let uu____20265 =
                                      let uu____20266 =
                                        FStar_List.hd
                                          lift_ct.FStar_Syntax_Syntax.effect_args
                                         in
                                      FStar_Pervasives_Native.fst uu____20266
                                       in
                                    (uu____20264, uu____20265)  in
                                  match uu____20259 with
                                  | (u1,wp) ->
                                      FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                        env u1
                                        lift_ct.FStar_Syntax_Syntax.result_typ
                                        wp FStar_Range.dummyRange
                                   in
                                (let uu____20292 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects"))
                                     &&
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme)
                                    in
                                 if uu____20292
                                 then
                                   let uu____20298 =
                                     FStar_Syntax_Print.term_to_string fml
                                      in
                                   FStar_Util.print1 "Guard for lift is: %s"
                                     uu____20298
                                 else ());
                                (let c1 =
                                   let uu____20304 =
                                     let uu____20305 =
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
                                         uu____20305;
                                       FStar_Syntax_Syntax.flags = []
                                     }  in
                                   FStar_Syntax_Syntax.mk_Comp uu____20304
                                    in
                                 (let uu____20329 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects")
                                     in
                                  if uu____20329
                                  then
                                    let uu____20334 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    FStar_Util.print1 "} Lifted comp: %s\n"
                                      uu____20334
                                  else ());
                                 (let uu____20339 =
                                    let uu____20340 =
                                      FStar_TypeChecker_Env.conj_guard g
                                        guard_f
                                       in
                                    let uu____20341 =
                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                        (FStar_TypeChecker_Common.NonTrivial
                                           fml)
                                       in
                                    FStar_TypeChecker_Env.conj_guard
                                      uu____20340 uu____20341
                                     in
                                  (c1, uu____20339)))))))))
  
let lift_tf_layered_effect_term :
  'uuuuuu20355 .
    'uuuuuu20355 ->
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
              let uu____20384 =
                let uu____20389 =
                  FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____20389
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____20384 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____20432 =
                let uu____20433 =
                  let uu____20436 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____20436
                    FStar_Syntax_Subst.compress
                   in
                uu____20433.FStar_Syntax_Syntax.n  in
              match uu____20432 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____20459::bs,uu____20461)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____20501 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____20501
                    FStar_Pervasives_Native.fst
              | uu____20607 ->
                  let uu____20608 =
                    let uu____20614 =
                      let uu____20616 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____20616
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____20614)  in
                  FStar_Errors.raise_error uu____20608
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____20643 = FStar_Syntax_Syntax.as_arg a  in
              let uu____20652 =
                let uu____20663 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____20699  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____20706 =
                  let uu____20717 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____20717]  in
                FStar_List.append uu____20663 uu____20706  in
              uu____20643 :: uu____20652  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              e.FStar_Syntax_Syntax.pos
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index  ->
        let uu____20788 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____20788 with
        | (uu____20793,t) ->
            let err n =
              let uu____20803 =
                let uu____20809 =
                  let uu____20811 = FStar_Ident.string_of_lid datacon  in
                  let uu____20813 = FStar_Util.string_of_int n  in
                  let uu____20815 = FStar_Util.string_of_int index  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____20811 uu____20813 uu____20815
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____20809)
                 in
              let uu____20819 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____20803 uu____20819  in
            let uu____20820 =
              let uu____20821 = FStar_Syntax_Subst.compress t  in
              uu____20821.FStar_Syntax_Syntax.n  in
            (match uu____20820 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____20825) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____20880  ->
                           match uu____20880 with
                           | (uu____20888,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____20897 -> true)))
                    in
                 if (FStar_List.length bs1) <= index
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index  in
                    FStar_Syntax_Util.mk_field_projector_name datacon
                      (FStar_Pervasives_Native.fst b) index)
             | uu____20931 -> err Prims.int_zero)
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub  ->
      let uu____20944 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub.FStar_Syntax_Syntax.target)
         in
      if uu____20944
      then
        let uu____20947 =
          let uu____20960 =
            FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub.FStar_Syntax_Syntax.target uu____20960
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____20947;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____20995 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____20995 with
           | (uu____21004,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____21023 =
                 let uu____21024 =
                   let uu___2484_21025 = ct  in
                   let uu____21026 =
                     let uu____21037 =
                       let uu____21046 =
                         let uu____21047 =
                           let uu____21048 =
                             let uu____21065 =
                               let uu____21076 =
                                 FStar_Syntax_Syntax.as_arg
                                   ct.FStar_Syntax_Syntax.result_typ
                                  in
                               [uu____21076; wp]  in
                             (lift_t, uu____21065)  in
                           FStar_Syntax_Syntax.Tm_app uu____21048  in
                         FStar_Syntax_Syntax.mk uu____21047
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____21046
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____21037]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2484_21025.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2484_21025.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____21026;
                     FStar_Syntax_Syntax.flags =
                       (uu___2484_21025.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____21024  in
               (uu____21023, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____21176 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____21176 with
           | (uu____21183,lift_t) ->
               let uu____21185 =
                 let uu____21186 =
                   let uu____21203 =
                     let uu____21214 = FStar_Syntax_Syntax.as_arg r  in
                     let uu____21223 =
                       let uu____21234 =
                         FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                          in
                       let uu____21243 =
                         let uu____21254 = FStar_Syntax_Syntax.as_arg e  in
                         [uu____21254]  in
                       uu____21234 :: uu____21243  in
                     uu____21214 :: uu____21223  in
                   (lift_t, uu____21203)  in
                 FStar_Syntax_Syntax.Tm_app uu____21186  in
               FStar_Syntax_Syntax.mk uu____21185 e.FStar_Syntax_Syntax.pos
            in
         let uu____21307 =
           let uu____21320 =
             FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____21320 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____21307;
           FStar_TypeChecker_Env.mlift_term =
             (match sub.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____21356  ->
                        fun uu____21357  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun sub  ->
      let uu____21380 = get_mlift_for_subeff env sub  in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub.FStar_Syntax_Syntax.source sub.FStar_Syntax_Syntax.target
        uu____21380
  
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
  