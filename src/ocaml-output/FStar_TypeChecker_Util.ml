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
                let rng = env.FStar_TypeChecker_Env.range  in
                let err uu____2361 =
                  let uu____2362 =
                    let uu____2368 =
                      let uu____2370 =
                        FStar_Syntax_Print.lid_to_string
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____2372 =
                        FStar_Syntax_Print.lid_to_string
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____2370
                        uu____2372
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____2368)
                     in
                  FStar_Errors.raise_error uu____2362 rng  in
                ((let uu____2387 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "LayeredEffects")
                     in
                  if uu____2387
                  then
                    let uu____2392 =
                      let uu____2394 =
                        FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp
                         in
                      FStar_All.pipe_right uu____2394
                        FStar_Syntax_Print.comp_to_string
                       in
                    let uu____2396 =
                      let uu____2398 =
                        FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                         in
                      FStar_All.pipe_right uu____2398
                        FStar_Syntax_Print.comp_to_string
                       in
                    let uu____2400 = FStar_Util.string_of_bool for_bind  in
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
                          ct.FStar_Syntax_Syntax.result_typ
                         in
                      let uu____2456 =
                        let uu____2461 =
                          FStar_TypeChecker_Env.push_bv env x_bv  in
                        let uu____2462 =
                          FStar_TypeChecker_Env.get_effect_decl env ret_eff
                           in
                        let uu____2463 =
                          FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
                        let uu____2464 = FStar_Syntax_Syntax.bv_to_name x_bv
                           in
                        mk_return uu____2461 uu____2462 uu____2463
                          ct.FStar_Syntax_Syntax.result_typ uu____2464 rng
                         in
                      match uu____2456 with
                      | (c_ret,g_ret) ->
                          let uu____2471 =
                            let uu____2476 =
                              FStar_Syntax_Util.comp_to_comp_typ c_ret  in
                            f_bind env ct (FStar_Pervasives_Native.Some x_bv)
                              uu____2476 [] rng
                             in
                          (match uu____2471 with
                           | (c,g_bind) ->
                               let uu____2483 =
                                 FStar_TypeChecker_Env.conj_guard g_ret
                                   g_bind
                                  in
                               (c, uu____2483))
                       in
                    let try_lift c12 c22 =
                      let p_bind_opt =
                        FStar_TypeChecker_Env.exists_polymonadic_bind env
                          c12.FStar_Syntax_Syntax.effect_name
                          c22.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____2528 =
                        FStar_All.pipe_right p_bind_opt FStar_Util.is_some
                         in
                      if uu____2528
                      then
                        let uu____2564 =
                          FStar_All.pipe_right p_bind_opt FStar_Util.must  in
                        match uu____2564 with
                        | (p,f_bind) ->
                            let uu____2631 =
                              FStar_Ident.lid_equals p
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            (if uu____2631
                             then
                               let uu____2644 = bind_with_return c12 p f_bind
                                  in
                               match uu____2644 with
                               | (c13,g) ->
                                   let uu____2661 =
                                     let uu____2670 =
                                       FStar_Syntax_Syntax.mk_Comp c22  in
                                     ((c22.FStar_Syntax_Syntax.effect_name),
                                       c13, uu____2670, g)
                                      in
                                   FStar_Pervasives_Native.Some uu____2661
                             else FStar_Pervasives_Native.None)
                      else FStar_Pervasives_Native.None  in
                    let uu____2699 =
                      let uu____2710 = try_lift c11 c21  in
                      match uu____2710 with
                      | FStar_Pervasives_Native.Some (p,c12,c22,g) ->
                          (p, c12, c22, g,
                            FStar_TypeChecker_Env.trivial_guard)
                      | FStar_Pervasives_Native.None  ->
                          let uu____2751 = try_lift c21 c11  in
                          (match uu____2751 with
                           | FStar_Pervasives_Native.Some (p,c22,c12,g) ->
                               (p, c12, c22,
                                 FStar_TypeChecker_Env.trivial_guard, g)
                           | FStar_Pervasives_Native.None  -> err ())
                       in
                    match uu____2699 with
                    | (p,c12,c22,g1,g2) ->
                        ((let uu____2808 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2808
                          then
                            let uu____2813 = FStar_Ident.string_of_lid p  in
                            let uu____2815 =
                              FStar_Syntax_Print.comp_to_string c12  in
                            let uu____2817 =
                              FStar_Syntax_Print.comp_to_string c22  in
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
  fun env  ->
    fun c1  ->
      fun c2  ->
        fun b  ->
          fun for_bind  ->
            let uu____2870 = lift_comps_sep_guards env c1 c2 b for_bind  in
            match uu____2870 with
            | (l,c11,c21,g1,g2) ->
                let uu____2894 = FStar_TypeChecker_Env.conj_guard g1 g2  in
                (l, c11, c21, uu____2894)
  
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
          let uu____2950 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____2950
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2962 =
      let uu____2963 = FStar_Syntax_Subst.compress t  in
      uu____2963.FStar_Syntax_Syntax.n  in
    match uu____2962 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2967 -> true
    | uu____2983 -> false
  
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
              let uu____3053 =
                let uu____3055 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____3055  in
              if uu____3053
              then f
              else (let uu____3062 = reason1 ()  in label uu____3062 r f)
  
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
            let uu___396_3083 = g  in
            let uu____3084 =
              let uu____3085 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____3085  in
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
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____3106 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____3106
        then c
        else
          (let uu____3111 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____3111
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close =
                  let uu____3153 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator
                     in
                  FStar_All.pipe_right uu____3153 FStar_Util.must  in
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____3182 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____3182]  in
                       let us =
                         let uu____3204 =
                           let uu____3207 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____3207]  in
                         u_res :: uu____3204  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____3213 =
                         FStar_TypeChecker_Env.inst_effect_fun_with us env md
                           close
                          in
                       let uu____3214 =
                         let uu____3215 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____3224 =
                           let uu____3235 =
                             FStar_Syntax_Syntax.as_arg
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____3244 =
                             let uu____3255 = FStar_Syntax_Syntax.as_arg wp1
                                in
                             [uu____3255]  in
                           uu____3235 :: uu____3244  in
                         uu____3215 :: uu____3224  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____3213 uu____3214
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____3297 = destruct_wp_comp c1  in
              match uu____3297 with
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
                let uu____3337 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____3337
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
                  let uu____3387 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs)
                     in
                  FStar_All.pipe_right uu____3387
                    (close_guard_implicits env false bs)))
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_3400  ->
            match uu___0_3400 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____3403 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____3428 =
            let uu____3431 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____3431 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____3428
            (fun c  ->
               (let uu____3455 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____3455) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____3459 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____3459)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____3470 = FStar_Syntax_Util.head_and_args' e  in
                match uu____3470 with
                | (head,uu____3487) ->
                    let uu____3508 =
                      let uu____3509 = FStar_Syntax_Util.un_uinst head  in
                      uu____3509.FStar_Syntax_Syntax.n  in
                    (match uu____3508 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____3514 =
                           let uu____3516 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____3516
                            in
                         Prims.op_Negation uu____3514
                     | uu____3517 -> true)))
              &&
              (let uu____3520 = should_not_inline_lc lc  in
               Prims.op_Negation uu____3520)
  
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
            let uu____3548 =
              let uu____3550 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____3550  in
            if uu____3548
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____3557 = FStar_Syntax_Util.is_unit t  in
               if uu____3557
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
                    let uu____3566 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____3566
                    then FStar_Syntax_Syntax.tun
                    else
                      (let ret_wp =
                         FStar_All.pipe_right m
                           FStar_Syntax_Util.get_return_vc_combinator
                          in
                       let uu____3572 =
                         let uu____3573 =
                           FStar_TypeChecker_Env.inst_effect_fun_with 
                             [u_t] env m ret_wp
                            in
                         let uu____3574 =
                           let uu____3575 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____3584 =
                             let uu____3595 = FStar_Syntax_Syntax.as_arg v
                                in
                             [uu____3595]  in
                           uu____3575 :: uu____3584  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3573 uu____3574
                           v.FStar_Syntax_Syntax.pos
                          in
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Env.Beta;
                         FStar_TypeChecker_Env.NoFullNorm] env uu____3572)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____3629 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____3629
           then
             let uu____3634 =
               FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos  in
             let uu____3636 = FStar_Syntax_Print.term_to_string v  in
             let uu____3638 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
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
                        let uu____3712 =
                          let uu____3714 =
                            FStar_All.pipe_right m FStar_Ident.ident_of_lid
                             in
                          FStar_All.pipe_right uu____3714
                            FStar_Ident.string_of_id
                           in
                        let uu____3716 =
                          let uu____3718 =
                            FStar_All.pipe_right n FStar_Ident.ident_of_lid
                             in
                          FStar_All.pipe_right uu____3718
                            FStar_Ident.string_of_id
                           in
                        let uu____3720 =
                          let uu____3722 =
                            FStar_All.pipe_right p FStar_Ident.ident_of_lid
                             in
                          FStar_All.pipe_right uu____3722
                            FStar_Ident.string_of_id
                           in
                        FStar_Util.format3 "(%s, %s) |> %s" uu____3712
                          uu____3716 uu____3720
                         in
                      (let uu____3726 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LayeredEffects")
                          in
                       if uu____3726
                       then
                         let uu____3731 =
                           let uu____3733 = FStar_Syntax_Syntax.mk_Comp ct1
                              in
                           FStar_Syntax_Print.comp_to_string uu____3733  in
                         let uu____3734 =
                           let uu____3736 = FStar_Syntax_Syntax.mk_Comp ct2
                              in
                           FStar_Syntax_Print.comp_to_string uu____3736  in
                         FStar_Util.print2 "Binding c1:%s and c2:%s {\n"
                           uu____3731 uu____3734
                       else ());
                      (let uu____3741 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "ResolveImplicitsHook")
                          in
                       if uu____3741
                       then
                         let uu____3746 =
                           let uu____3748 =
                             FStar_TypeChecker_Env.get_range env  in
                           FStar_Range.string_of_range uu____3748  in
                         let uu____3749 =
                           FStar_Syntax_Print.tscheme_to_string bind_t  in
                         FStar_Util.print2
                           "///////////////////////////////Bind at %s/////////////////////\nwith bind_t = %s\n"
                           uu____3746 uu____3749
                       else ());
                      (let uu____3754 =
                         let uu____3761 =
                           FStar_TypeChecker_Env.get_effect_decl env m  in
                         let uu____3762 =
                           FStar_TypeChecker_Env.get_effect_decl env n  in
                         let uu____3763 =
                           FStar_TypeChecker_Env.get_effect_decl env p  in
                         (uu____3761, uu____3762, uu____3763)  in
                       match uu____3754 with
                       | (m_ed,n_ed,p_ed) ->
                           let uu____3771 =
                             let uu____3784 =
                               FStar_List.hd
                                 ct1.FStar_Syntax_Syntax.comp_univs
                                in
                             let uu____3785 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 ct1.FStar_Syntax_Syntax.effect_args
                                in
                             (uu____3784,
                               (ct1.FStar_Syntax_Syntax.result_typ),
                               uu____3785)
                              in
                           (match uu____3771 with
                            | (u1,t1,is1) ->
                                let uu____3829 =
                                  let uu____3842 =
                                    FStar_List.hd
                                      ct2.FStar_Syntax_Syntax.comp_univs
                                     in
                                  let uu____3843 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst
                                      ct2.FStar_Syntax_Syntax.effect_args
                                     in
                                  (uu____3842,
                                    (ct2.FStar_Syntax_Syntax.result_typ),
                                    uu____3843)
                                   in
                                (match uu____3829 with
                                 | (u2,t2,is2) ->
                                     let uu____3887 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         bind_t [u1; u2]
                                        in
                                     (match uu____3887 with
                                      | (uu____3896,bind_t1) ->
                                          let bind_t_shape_error s =
                                            let uu____3911 =
                                              let uu____3913 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t1
                                                 in
                                              FStar_Util.format3
                                                "bind %s (%s) does not have proper shape (reason:%s)"
                                                uu____3913 bind_name s
                                               in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu____3911)
                                             in
                                          let uu____3917 =
                                            let uu____3962 =
                                              let uu____3963 =
                                                FStar_Syntax_Subst.compress
                                                  bind_t1
                                                 in
                                              uu____3963.FStar_Syntax_Syntax.n
                                               in
                                            match uu____3962 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs,c) when
                                                (FStar_List.length bs) >=
                                                  (Prims.of_int (4))
                                                ->
                                                let uu____4039 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs c
                                                   in
                                                (match uu____4039 with
                                                 | (a_b::b_b::bs1,c1) ->
                                                     let uu____4124 =
                                                       let uu____4151 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2)))
                                                           bs1
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____4151
                                                         (fun uu____4236  ->
                                                            match uu____4236
                                                            with
                                                            | (l1,l2) ->
                                                                let uu____4317
                                                                  =
                                                                  FStar_List.hd
                                                                    l2
                                                                   in
                                                                let uu____4330
                                                                  =
                                                                  let uu____4337
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                  FStar_List.hd
                                                                    uu____4337
                                                                   in
                                                                (l1,
                                                                  uu____4317,
                                                                  uu____4330))
                                                        in
                                                     (match uu____4124 with
                                                      | (rest_bs,f_b,g_b) ->
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b, c1)))
                                            | uu____4497 ->
                                                let uu____4498 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders"
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____4498 r1
                                             in
                                          (match uu____3917 with
                                           | (a_b,b_b,rest_bs,f_b,g_b,bind_c)
                                               ->
                                               let uu____4623 =
                                                 let uu____4630 =
                                                   let uu____4631 =
                                                     let uu____4632 =
                                                       let uu____4639 =
                                                         FStar_All.pipe_right
                                                           a_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       (uu____4639, t1)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____4632
                                                      in
                                                   let uu____4650 =
                                                     let uu____4653 =
                                                       let uu____4654 =
                                                         let uu____4661 =
                                                           FStar_All.pipe_right
                                                             b_b
                                                             FStar_Pervasives_Native.fst
                                                            in
                                                         (uu____4661, t2)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____4654
                                                        in
                                                     [uu____4653]  in
                                                   uu____4631 :: uu____4650
                                                    in
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs uu____4630
                                                   (fun b1  ->
                                                      let uu____4676 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1
                                                         in
                                                      let uu____4678 =
                                                        FStar_Range.string_of_range
                                                          r1
                                                         in
                                                      FStar_Util.format3
                                                        "implicit var for binder %s of %s at %s"
                                                        uu____4676 bind_name
                                                        uu____4678) r1
                                                  in
                                               (match uu____4623 with
                                                | (rest_bs_uvars,g_uvars) ->
                                                    ((let uu____4692 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "ResolveImplicitsHook")
                                                         in
                                                      if uu____4692
                                                      then
                                                        FStar_All.pipe_right
                                                          rest_bs_uvars
                                                          (FStar_List.iter
                                                             (fun t  ->
                                                                let uu____4706
                                                                  =
                                                                  let uu____4707
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    t  in
                                                                  uu____4707.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____4706
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (u,uu____4711)
                                                                    ->
                                                                    let uu____4728
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t  in
                                                                    let uu____4730
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
                                                                    uu____4736
                                                                    ->
                                                                    "<no attr>"
                                                                     in
                                                                    FStar_Util.print2
                                                                    "Generated uvar %s with attribute %s\n"
                                                                    uu____4728
                                                                    uu____4730))
                                                      else ());
                                                     (let subst =
                                                        FStar_List.map2
                                                          (fun b1  ->
                                                             fun t  ->
                                                               let uu____4767
                                                                 =
                                                                 let uu____4774
                                                                   =
                                                                   FStar_All.pipe_right
                                                                    b1
                                                                    FStar_Pervasives_Native.fst
                                                                    in
                                                                 (uu____4774,
                                                                   t)
                                                                  in
                                                               FStar_Syntax_Syntax.NT
                                                                 uu____4767)
                                                          (a_b :: b_b ::
                                                          rest_bs) (t1 :: t2
                                                          :: rest_bs_uvars)
                                                         in
                                                      let f_guard =
                                                        let f_sort_is =
                                                          let uu____4803 =
                                                            let uu____4806 =
                                                              let uu____4807
                                                                =
                                                                let uu____4808
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    f_b
                                                                    FStar_Pervasives_Native.fst
                                                                   in
                                                                uu____4808.FStar_Syntax_Syntax.sort
                                                                 in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4807
                                                               in
                                                            let uu____4817 =
                                                              FStar_Syntax_Util.is_layered
                                                                m_ed
                                                               in
                                                            effect_args_from_repr
                                                              uu____4806
                                                              uu____4817 r1
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____4803
                                                            (FStar_List.map
                                                               (FStar_Syntax_Subst.subst
                                                                  subst))
                                                           in
                                                        FStar_List.fold_left2
                                                          (fun g  ->
                                                             fun i1  ->
                                                               fun f_i1  ->
                                                                 (let uu____4842
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "ResolveImplicitsHook")
                                                                     in
                                                                  if
                                                                    uu____4842
                                                                  then
                                                                    let uu____4847
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    i1  in
                                                                    let uu____4849
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    f_i1  in
                                                                    FStar_Util.print2
                                                                    "Generating constraint %s = %s\n"
                                                                    uu____4847
                                                                    uu____4849
                                                                  else ());
                                                                 (let uu____4854
                                                                    =
                                                                    FStar_TypeChecker_Rel.layered_effect_teq
                                                                    env i1
                                                                    f_i1
                                                                    (FStar_Pervasives_Native.Some
                                                                    bind_name)
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____4854))
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
                                                          let uu____4874 =
                                                            let uu____4875 =
                                                              let uu____4878
                                                                =
                                                                let uu____4879
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    g_b
                                                                    FStar_Pervasives_Native.fst
                                                                   in
                                                                uu____4879.FStar_Syntax_Syntax.sort
                                                                 in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4878
                                                               in
                                                            uu____4875.FStar_Syntax_Syntax.n
                                                             in
                                                          match uu____4874
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_arrow
                                                              (bs,c) ->
                                                              let uu____4912
                                                                =
                                                                FStar_Syntax_Subst.open_comp
                                                                  bs c
                                                                 in
                                                              (match uu____4912
                                                               with
                                                               | (bs1,c1) ->
                                                                   let bs_subst
                                                                    =
                                                                    let uu____4922
                                                                    =
                                                                    let uu____4929
                                                                    =
                                                                    let uu____4930
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____4930
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____4951
                                                                    =
                                                                    let uu____4954
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4954
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____4929,
                                                                    uu____4951)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4922
                                                                     in
                                                                   let c2 =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1  in
                                                                   let uu____4968
                                                                    =
                                                                    let uu____4971
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2)  in
                                                                    let uu____4972
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed  in
                                                                    effect_args_from_repr
                                                                    uu____4971
                                                                    uu____4972
                                                                    r1  in
                                                                   FStar_All.pipe_right
                                                                    uu____4968
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst)))
                                                          | uu____4978 ->
                                                              failwith
                                                                "impossible: mk_indexed_bind"
                                                           in
                                                        let env_g =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env [x_a]
                                                           in
                                                        let uu____4995 =
                                                          FStar_List.fold_left2
                                                            (fun g  ->
                                                               fun i1  ->
                                                                 fun g_i1  ->
                                                                   (let uu____5013
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "ResolveImplicitsHook")
                                                                     in
                                                                    if
                                                                    uu____5013
                                                                    then
                                                                    let uu____5018
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    i1  in
                                                                    let uu____5020
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    g_i1  in
                                                                    FStar_Util.print2
                                                                    "Generating constraint %s = %s\n"
                                                                    uu____5018
                                                                    uu____5020
                                                                    else ());
                                                                   (let uu____5025
                                                                    =
                                                                    FStar_TypeChecker_Rel.layered_effect_teq
                                                                    env_g i1
                                                                    g_i1
                                                                    (FStar_Pervasives_Native.Some
                                                                    bind_name)
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____5025))
                                                            FStar_TypeChecker_Env.trivial_guard
                                                            is2 g_sort_is
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____4995
                                                          (FStar_TypeChecker_Env.close_guard
                                                             env [x_a])
                                                         in
                                                      let bind_ct =
                                                        let uu____5040 =
                                                          FStar_All.pipe_right
                                                            bind_c
                                                            (FStar_Syntax_Subst.subst_comp
                                                               subst)
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____5040
                                                          FStar_Syntax_Util.comp_to_comp_typ
                                                         in
                                                      let fml =
                                                        let uu____5042 =
                                                          let uu____5047 =
                                                            FStar_List.hd
                                                              bind_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____5048 =
                                                            let uu____5049 =
                                                              FStar_List.hd
                                                                bind_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____5049
                                                             in
                                                          (uu____5047,
                                                            uu____5048)
                                                           in
                                                        match uu____5042 with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              bind_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let is =
                                                        let uu____5075 =
                                                          FStar_Syntax_Subst.compress
                                                            bind_ct.FStar_Syntax_Syntax.result_typ
                                                           in
                                                        let uu____5076 =
                                                          FStar_Syntax_Util.is_layered
                                                            p_ed
                                                           in
                                                        effect_args_from_repr
                                                          uu____5075
                                                          uu____5076 r1
                                                         in
                                                      let c =
                                                        let uu____5079 =
                                                          let uu____5080 =
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
                                                              = uu____5080;
                                                            FStar_Syntax_Syntax.flags
                                                              = flags
                                                          }  in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____5079
                                                         in
                                                      (let uu____5100 =
                                                         FStar_All.pipe_left
                                                           (FStar_TypeChecker_Env.debug
                                                              env)
                                                           (FStar_Options.Other
                                                              "LayeredEffects")
                                                          in
                                                       if uu____5100
                                                       then
                                                         let uu____5105 =
                                                           FStar_Syntax_Print.comp_to_string
                                                             c
                                                            in
                                                         FStar_Util.print1
                                                           "} c after bind: %s\n"
                                                           uu____5105
                                                       else ());
                                                      (let guard =
                                                         let uu____5111 =
                                                           let uu____5114 =
                                                             let uu____5117 =
                                                               let uu____5120
                                                                 =
                                                                 let uu____5123
                                                                   =
                                                                   FStar_TypeChecker_Env.guard_of_guard_formula
                                                                    (FStar_TypeChecker_Common.NonTrivial
                                                                    fml)
                                                                    in
                                                                 [uu____5123]
                                                                  in
                                                               g_guard ::
                                                                 uu____5120
                                                                in
                                                             f_guard ::
                                                               uu____5117
                                                              in
                                                           g_uvars ::
                                                             uu____5114
                                                            in
                                                         FStar_TypeChecker_Env.conj_guards
                                                           uu____5111
                                                          in
                                                       (let uu____5125 =
                                                          FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "ResolveImplicitsHook")
                                                           in
                                                        if uu____5125
                                                        then
                                                          let uu____5130 =
                                                            let uu____5132 =
                                                              FStar_TypeChecker_Env.get_range
                                                                env
                                                               in
                                                            FStar_Range.string_of_range
                                                              uu____5132
                                                             in
                                                          let uu____5133 =
                                                            FStar_TypeChecker_Rel.guard_to_string
                                                              env guard
                                                             in
                                                          FStar_Util.print2
                                                            "///////////////////////////////EndBind at %s/////////////////////\nguard = %s\n"
                                                            uu____5130
                                                            uu____5133
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
                let uu____5182 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____5208 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____5208 with
                  | (a,kwp) ->
                      let uu____5239 = destruct_wp_comp ct1  in
                      let uu____5246 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____5239, uu____5246)
                   in
                match uu____5182 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____5299 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____5299]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____5319 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____5319]
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
                      let uu____5366 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____5375 =
                        let uu____5386 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____5395 =
                          let uu____5406 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____5415 =
                            let uu____5426 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____5435 =
                              let uu____5446 =
                                let uu____5455 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____5455  in
                              [uu____5446]  in
                            uu____5426 :: uu____5435  in
                          uu____5406 :: uu____5415  in
                        uu____5386 :: uu____5395  in
                      uu____5366 :: uu____5375  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____5506 =
                        FStar_TypeChecker_Env.inst_effect_fun_with
                          [u_t1; u_t2] env md bind_wp
                         in
                      FStar_Syntax_Syntax.mk_Tm_app uu____5506 wp_args
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
              let uu____5554 =
                let uu____5559 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
                let uu____5560 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
                (uu____5559, uu____5560)  in
              match uu____5554 with
              | (ct1,ct2) ->
                  let uu____5567 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name
                     in
                  (match uu____5567 with
                   | FStar_Pervasives_Native.Some (p,f_bind) ->
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None  ->
                       let uu____5618 = lift_comps env c1 c2 b true  in
                       (match uu____5618 with
                        | (m,c11,c21,g_lift) ->
                            let uu____5636 =
                              let uu____5641 =
                                FStar_Syntax_Util.comp_to_comp_typ c11  in
                              let uu____5642 =
                                FStar_Syntax_Util.comp_to_comp_typ c21  in
                              (uu____5641, uu____5642)  in
                            (match uu____5636 with
                             | (ct11,ct21) ->
                                 let uu____5649 =
                                   let uu____5654 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m
                                      in
                                   if uu____5654
                                   then
                                     let bind_t =
                                       let uu____5662 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env)
                                          in
                                       FStar_All.pipe_right uu____5662
                                         FStar_Syntax_Util.get_bind_vc_combinator
                                        in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu____5665 =
                                        mk_wp_bind env m ct11 b ct21 flags r1
                                         in
                                      (uu____5665,
                                        FStar_TypeChecker_Env.trivial_guard))
                                    in
                                 (match uu____5649 with
                                  | (c,g_bind) ->
                                      let uu____5672 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind
                                         in
                                      (c, uu____5672)))))
  
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
            let uu____5708 =
              let uu____5709 =
                let uu____5720 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____5720]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____5709;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____5708  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____5765 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_5771  ->
              match uu___1_5771 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5774 -> false))
       in
    if uu____5765
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_5786  ->
              match uu___2_5786 with
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
        let uu____5814 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5814
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____5825 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____5825  in
           let pure_assume_wp1 =
             let uu____5828 =
               let uu____5829 =
                 FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
               [uu____5829]  in
             let uu____5862 = FStar_TypeChecker_Env.get_range env  in
             FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____5828
               uu____5862
              in
           let uu____5863 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____5863)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5891 =
          let uu____5892 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5892 with
          | (c,g_c) ->
              let uu____5903 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5903
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5917 = weaken_comp env c f1  in
                     (match uu____5917 with
                      | (c1,g_w) ->
                          let uu____5928 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____5928)))
           in
        let uu____5929 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5929 weaken
  
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
                 let uu____5986 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____5986  in
               let pure_assert_wp1 =
                 let uu____5989 =
                   let uu____5990 =
                     let uu____5999 = label_opt env reason r f  in
                     FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                       uu____5999
                      in
                   [uu____5990]  in
                 FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____5989 r
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
            let uu____6069 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____6069
            then (lc, g0)
            else
              (let flags =
                 let uu____6081 =
                   let uu____6089 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____6089
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____6081 with
                 | (maybe_trivial_post,flags) ->
                     let uu____6119 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_6127  ->
                               match uu___3_6127 with
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
                               | uu____6130 -> []))
                        in
                     FStar_List.append flags uu____6119
                  in
               let strengthen uu____6140 =
                 let uu____6141 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____6141 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____6160 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____6160 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____6167 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____6167
                              then
                                let uu____6171 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____6173 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____6171 uu____6173
                              else ());
                             (let uu____6178 =
                                strengthen_comp env reason c f flags  in
                              match uu____6178 with
                              | (c1,g_s) ->
                                  let uu____6189 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____6189))))
                  in
               let uu____6190 =
                 let uu____6191 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____6191
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____6190,
                 (let uu___728_6193 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred_to_tac =
                      (uu___728_6193.FStar_TypeChecker_Common.deferred_to_tac);
                    FStar_TypeChecker_Common.deferred =
                      (uu___728_6193.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___728_6193.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___728_6193.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_6202  ->
            match uu___4_6202 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____6206 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____6235 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____6235
          then e
          else
            (let uu____6242 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____6245 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____6245)
                in
             if uu____6242
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
                | uu____6315 -> false  in
              if is_unit
              then
                let uu____6322 =
                  let uu____6324 =
                    let uu____6325 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____6325
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____6324
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____6322
                 then
                   let uu____6334 = FStar_Syntax_Subst.open_term_bv b phi  in
                   match uu____6334 with
                   | (b1,phi1) ->
                       let phi2 =
                         FStar_Syntax_Subst.subst
                           [FStar_Syntax_Syntax.NT
                              (b1, FStar_Syntax_Syntax.unit_const)] phi1
                          in
                       weaken_comp env c phi2
                 else
                   (let uu____6350 = close_wp_comp env [x] c  in
                    (uu____6350, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____6353 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
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
          fun uu____6381  ->
            match uu____6381 with
            | (b,lc2) ->
                let debug f =
                  let uu____6401 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____6401 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____6414 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____6414
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____6424 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____6424
                       then
                         let uu____6429 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____6429
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____6436 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____6436
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____6445 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____6445
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____6452 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____6452
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____6468 =
                  let uu____6469 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____6469
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____6477 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____6477, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____6480 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____6480 with
                     | (c1,g_c1) ->
                         let uu____6491 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____6491 with
                          | (c2,g_c2) ->
                              let trivial_guard =
                                let uu____6503 =
                                  match b with
                                  | FStar_Pervasives_Native.Some x ->
                                      let b1 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      let uu____6506 =
                                        FStar_Syntax_Syntax.is_null_binder b1
                                         in
                                      if uu____6506
                                      then g_c2
                                      else
                                        FStar_TypeChecker_Env.close_guard env
                                          [b1] g_c2
                                  | FStar_Pervasives_Native.None  -> g_c2  in
                                FStar_TypeChecker_Env.conj_guard g_c1
                                  uu____6503
                                 in
                              (debug
                                 (fun uu____6532  ->
                                    let uu____6533 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____6535 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____6540 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____6533 uu____6535 uu____6540);
                               (let aux uu____6558 =
                                  let uu____6559 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____6559
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____6590
                                        ->
                                        let uu____6591 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____6591
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____6623 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____6623
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____6670 =
                                  let aux_with_trivial_guard uu____6700 =
                                    let uu____6701 = aux ()  in
                                    match uu____6701 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c, trivial_guard, reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____6759 =
                                    let uu____6761 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____6761  in
                                  if uu____6759
                                  then
                                    let uu____6777 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____6777
                                     then
                                       FStar_Util.Inl
                                         (c2, trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____6804 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____6804))
                                  else
                                    (let uu____6821 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____6821
                                     then
                                       let close_with_type_of_x x c =
                                         let x1 =
                                           let uu___831_6852 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___831_6852.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___831_6852.FStar_Syntax_Syntax.index);
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
                                           let uu____6883 =
                                             let uu____6888 =
                                               FStar_All.pipe_right c2
                                                 (FStar_Syntax_Subst.subst_comp
                                                    [FStar_Syntax_Syntax.NT
                                                       (x, e)])
                                                in
                                             FStar_All.pipe_right uu____6888
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6883 with
                                            | (c21,g_close) ->
                                                let uu____6909 =
                                                  let uu____6917 =
                                                    let uu____6918 =
                                                      let uu____6921 =
                                                        let uu____6924 =
                                                          FStar_TypeChecker_Env.map_guard
                                                            g_c2
                                                            (FStar_Syntax_Subst.subst
                                                               [FStar_Syntax_Syntax.NT
                                                                  (x, e)])
                                                           in
                                                        [uu____6924; g_close]
                                                         in
                                                      g_c1 :: uu____6921  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6918
                                                     in
                                                  (c21, uu____6917, "c1 Tot")
                                                   in
                                                FStar_Util.Inl uu____6909)
                                       | (uu____6937,FStar_Pervasives_Native.Some
                                          x) ->
                                           let uu____6949 =
                                             FStar_All.pipe_right c2
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6949 with
                                            | (c21,g_close) ->
                                                let uu____6972 =
                                                  let uu____6980 =
                                                    let uu____6981 =
                                                      let uu____6984 =
                                                        let uu____6987 =
                                                          let uu____6988 =
                                                            let uu____6989 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____6989]  in
                                                          FStar_TypeChecker_Env.close_guard
                                                            env uu____6988
                                                            g_c2
                                                           in
                                                        [uu____6987; g_close]
                                                         in
                                                      g_c1 :: uu____6984  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6981
                                                     in
                                                  (c21, uu____6980,
                                                    "c1 Tot only close")
                                                   in
                                                FStar_Util.Inl uu____6972)
                                       | (uu____7018,uu____7019) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____7034 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____7034
                                        then
                                          let uu____7049 =
                                            let uu____7057 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____7057, trivial_guard,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____7049
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____7070 = try_simplify ()  in
                                match uu____7070 with
                                | FStar_Util.Inl (c,g,reason) ->
                                    (debug
                                       (fun uu____7105  ->
                                          let uu____7106 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____7106);
                                     (c, g))
                                | FStar_Util.Inr reason ->
                                    (debug
                                       (fun uu____7122  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 g =
                                        let uu____7153 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____7153 with
                                        | (c,g_bind) ->
                                            let uu____7164 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g g_bind
                                               in
                                            (c, uu____7164)
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
                                        let uu____7191 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____7191 with
                                        | (m,uu____7203,lift2) ->
                                            let uu____7205 =
                                              lift_comp env c22 lift2  in
                                            (match uu____7205 with
                                             | (c23,g2) ->
                                                 let uu____7216 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____7216 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let trivial =
                                                        let uu____7232 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7232
                                                          FStar_Util.must
                                                         in
                                                      let vc1 =
                                                        let uu____7240 =
                                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                                            [u1] env
                                                            md_pure_or_ghost
                                                            trivial
                                                           in
                                                        let uu____7241 =
                                                          let uu____7242 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              t1
                                                             in
                                                          let uu____7251 =
                                                            let uu____7262 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                wp1
                                                               in
                                                            [uu____7262]  in
                                                          uu____7242 ::
                                                            uu____7251
                                                           in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7240
                                                          uu____7241 r1
                                                         in
                                                      let uu____7295 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____7295 with
                                                       | (c,g_s) ->
                                                           let uu____7310 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____7310))))
                                         in
                                      let uu____7311 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____7327 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____7327, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____7311 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____7343 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____7343
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____7352 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____7352
                                             then
                                               (debug
                                                  (fun uu____7366  ->
                                                     let uu____7367 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____7369 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____7367 uu____7369);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 let g =
                                                   let uu____7376 =
                                                     FStar_TypeChecker_Env.map_guard
                                                       g_c2
                                                       (FStar_Syntax_Subst.subst
                                                          [FStar_Syntax_Syntax.NT
                                                             (x, e1)])
                                                      in
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 uu____7376
                                                    in
                                                 mk_bind1 c1 b c21 g))
                                             else
                                               (let uu____7381 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____7384 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____7384)
                                                   in
                                                if uu____7381
                                                then
                                                  let e1' =
                                                    let uu____7409 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____7409
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug
                                                     (fun uu____7421  ->
                                                        let uu____7422 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____7424 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____7422
                                                          uu____7424);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug
                                                     (fun uu____7439  ->
                                                        let uu____7440 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____7442 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____7440
                                                          uu____7442);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____7449 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____7449
                                                       in
                                                    let uu____7450 =
                                                      let uu____7455 =
                                                        let uu____7456 =
                                                          let uu____7457 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____7457]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____7456
                                                         in
                                                      weaken_comp uu____7455
                                                        c21 x_eq_e
                                                       in
                                                    match uu____7450 with
                                                    | (c22,g_w) ->
                                                        let g =
                                                          let uu____7483 =
                                                            let uu____7484 =
                                                              let uu____7485
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x
                                                                 in
                                                              [uu____7485]
                                                               in
                                                            let uu____7504 =
                                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                                g_c2 x_eq_e
                                                               in
                                                            FStar_TypeChecker_Env.close_guard
                                                              env uu____7484
                                                              uu____7504
                                                             in
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g_c1 uu____7483
                                                           in
                                                        let uu____7505 =
                                                          mk_bind1 c1 b c22 g
                                                           in
                                                        (match uu____7505
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____7516 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____7516))))))
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
      | uu____7533 -> g2
  
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
            (let uu____7557 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____7557)
           in
        let flags =
          if should_return1
          then
            let uu____7565 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____7565
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine uu____7583 =
          let uu____7584 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____7584 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____7597 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____7597
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____7605 =
                  let uu____7607 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____7607  in
                (if uu____7605
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___956_7616 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___956_7616.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___956_7616.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___956_7616.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____7617 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____7617, g_c)
                 else
                   (let uu____7620 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____7620, g_c)))
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
                   let uu____7631 =
                     let uu____7632 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____7632
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____7631
                    in
                 let eq = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret
                     (FStar_TypeChecker_Common.NonTrivial eq)
                    in
                 let uu____7635 =
                   let uu____7640 =
                     let uu____7641 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____7641
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____7640  in
                 match uu____7635 with
                 | (bind_c,g_bind) ->
                     let uu____7650 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____7651 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____7650, uu____7651))
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
            fun uu____7687  ->
              match uu____7687 with
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
                    let uu____7699 =
                      ((let uu____7703 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____7703) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____7699
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____7721 =
        let uu____7722 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____7722  in
      FStar_Syntax_Syntax.fvar uu____7721 FStar_Syntax_Syntax.delta_constant
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
                    let uu____7774 =
                      FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname
                       in
                    FStar_Util.format1 "%s.conjunction" uu____7774  in
                  let uu____7777 =
                    let uu____7782 =
                      let uu____7783 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____7783 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7782 [u_a]
                     in
                  match uu____7777 with
                  | (uu____7794,conjunction) ->
                      let uu____7796 =
                        let uu____7805 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____7820 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____7805, uu____7820)  in
                      (match uu____7796 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____7866 =
                               let uu____7868 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format3
                                 "conjunction %s (%s) does not have proper shape (reason:%s)"
                                 uu____7868 conjunction_name s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7866)
                              in
                           let uu____7872 =
                             let uu____7917 =
                               let uu____7918 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____7918.FStar_Syntax_Syntax.n  in
                             match uu____7917 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____7967) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____7999 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____7999 with
                                  | (a_b::bs1,body1) ->
                                      let uu____8071 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____8071 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____8219 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____8219)))
                             | uu____8252 ->
                                 let uu____8253 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____8253 r
                              in
                           (match uu____7872 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____8378 =
                                  let uu____8385 =
                                    let uu____8386 =
                                      let uu____8387 =
                                        let uu____8394 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____8394, a)  in
                                      FStar_Syntax_Syntax.NT uu____8387  in
                                    [uu____8386]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____8385
                                    (fun b  ->
                                       let uu____8410 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____8412 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____8414 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____8410 uu____8412 uu____8414) r
                                   in
                                (match uu____8378 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____8452 =
                                                let uu____8459 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____8459, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____8452) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____8498 =
                                           let uu____8499 =
                                             let uu____8502 =
                                               let uu____8503 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8503.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8502
                                              in
                                           uu____8499.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8498 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8514,uu____8515::is) ->
                                             let uu____8557 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8557
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8590 ->
                                             let uu____8591 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8591 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____8607 =
                                                  FStar_TypeChecker_Rel.layered_effect_teq
                                                    env i1 f_i
                                                    (FStar_Pervasives_Native.Some
                                                       conjunction_name)
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8607)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____8613 =
                                           let uu____8614 =
                                             let uu____8617 =
                                               let uu____8618 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8618.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8617
                                              in
                                           uu____8614.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8613 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8629,uu____8630::is) ->
                                             let uu____8672 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8672
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8705 ->
                                             let uu____8706 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8706 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____8722 =
                                                  FStar_TypeChecker_Rel.layered_effect_teq
                                                    env i2 g_i
                                                    (FStar_Pervasives_Native.Some
                                                       conjunction_name)
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8722)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____8728 =
                                         let uu____8729 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____8729.FStar_Syntax_Syntax.n  in
                                       match uu____8728 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8734,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8789 ->
                                           let uu____8790 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____8790 r
                                        in
                                     let uu____8799 =
                                       let uu____8800 =
                                         let uu____8801 =
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
                                             uu____8801;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____8800
                                        in
                                     let uu____8824 =
                                       let uu____8825 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8825 g_guard
                                        in
                                     (uu____8799, uu____8824))))
  
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
                fun uu____8870  ->
                  let if_then_else =
                    let uu____8876 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____8876 FStar_Util.must  in
                  let uu____8883 = destruct_wp_comp ct1  in
                  match uu____8883 with
                  | (uu____8894,uu____8895,wp_t) ->
                      let uu____8897 = destruct_wp_comp ct2  in
                      (match uu____8897 with
                       | (uu____8908,uu____8909,wp_e) ->
                           let wp =
                             let uu____8912 =
                               FStar_TypeChecker_Env.inst_effect_fun_with
                                 [u_a] env ed if_then_else
                                in
                             let uu____8913 =
                               let uu____8914 = FStar_Syntax_Syntax.as_arg a
                                  in
                               let uu____8923 =
                                 let uu____8934 =
                                   FStar_Syntax_Syntax.as_arg p  in
                                 let uu____8943 =
                                   let uu____8954 =
                                     FStar_Syntax_Syntax.as_arg wp_t  in
                                   let uu____8963 =
                                     let uu____8974 =
                                       FStar_Syntax_Syntax.as_arg wp_e  in
                                     [uu____8974]  in
                                   uu____8954 :: uu____8963  in
                                 uu____8934 :: uu____8943  in
                               uu____8914 :: uu____8923  in
                             let uu____9023 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Syntax.mk_Tm_app uu____8912
                               uu____8913 uu____9023
                              in
                           let uu____9024 = mk_comp ed u_a a wp []  in
                           (uu____9024, FStar_TypeChecker_Env.trivial_guard))
  
let (comp_pure_wp_false :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun u  ->
      fun t  ->
        let post_k =
          let uu____9044 =
            let uu____9053 = FStar_Syntax_Syntax.null_binder t  in
            [uu____9053]  in
          let uu____9072 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
          FStar_Syntax_Util.arrow uu____9044 uu____9072  in
        let kwp =
          let uu____9078 =
            let uu____9087 = FStar_Syntax_Syntax.null_binder post_k  in
            [uu____9087]  in
          let uu____9106 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
          FStar_Syntax_Util.arrow uu____9078 uu____9106  in
        let post =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k  in
        let wp =
          let uu____9113 =
            let uu____9114 = FStar_Syntax_Syntax.mk_binder post  in
            [uu____9114]  in
          let uu____9133 = fvar_const env FStar_Parser_Const.false_lid  in
          FStar_Syntax_Util.abs uu____9113 uu____9133
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
            let uu____9192 =
              let uu____9193 =
                FStar_All.pipe_right scrutinee FStar_Syntax_Syntax.mk_binder
                 in
              [uu____9193]  in
            FStar_TypeChecker_Env.push_binders env0 uu____9192  in
          let eff =
            FStar_List.fold_left
              (fun eff  ->
                 fun uu____9240  ->
                   match uu____9240 with
                   | (uu____9254,eff_label,uu____9256,uu____9257) ->
                       join_effects env eff eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases
             in
          let uu____9270 =
            let uu____9278 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu____9316  ->
                      match uu____9316 with
                      | (uu____9331,uu____9332,flags,uu____9334) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___5_9351  ->
                                  match uu___5_9351 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                      true
                                  | uu____9354 -> false))))
               in
            if uu____9278
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, [])  in
          match uu____9270 with
          | (should_not_inline_whole_match,bind_cases_flags) ->
              let bind_cases uu____9391 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                   in
                let uu____9393 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                   in
                if uu____9393
                then
                  let uu____9400 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                     in
                  (uu____9400, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let maybe_return eff_label_then cthen =
                     let uu____9421 =
                       should_not_inline_whole_match ||
                         (let uu____9424 = is_pure_or_ghost_effect env eff
                             in
                          Prims.op_Negation uu____9424)
                        in
                     if uu____9421 then cthen true else cthen false  in
                   let uu____9431 =
                     let uu____9442 =
                       let uu____9455 =
                         let uu____9460 =
                           let uu____9471 =
                             FStar_All.pipe_right lcases
                               (FStar_List.map
                                  (fun uu____9521  ->
                                     match uu____9521 with
                                     | (g,uu____9540,uu____9541,uu____9542)
                                         -> g))
                              in
                           FStar_All.pipe_right uu____9471
                             (FStar_List.fold_left
                                (fun uu____9590  ->
                                   fun g  ->
                                     match uu____9590 with
                                     | (conds,acc) ->
                                         let cond =
                                           let uu____9631 =
                                             FStar_Syntax_Util.mk_neg g  in
                                           FStar_Syntax_Util.mk_conj acc
                                             uu____9631
                                            in
                                         ((FStar_List.append conds [cond]),
                                           cond))
                                ([FStar_Syntax_Util.t_true],
                                  FStar_Syntax_Util.t_true))
                            in
                         FStar_All.pipe_right uu____9460
                           FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____9455
                         (fun l  ->
                            FStar_List.splitAt
                              ((FStar_List.length l) - Prims.int_one) l)
                        in
                     FStar_All.pipe_right uu____9442
                       (fun uu____9729  ->
                          match uu____9729 with
                          | (l1,l2) ->
                              let uu____9770 = FStar_List.hd l2  in
                              (l1, uu____9770))
                      in
                   match uu____9431 with
                   | (neg_branch_conds,exhaustiveness_branch_cond) ->
                       let uu____9799 =
                         match lcases with
                         | [] ->
                             let uu____9830 =
                               comp_pure_wp_false env u_res_t res_t  in
                             (FStar_Pervasives_Native.None, uu____9830,
                               FStar_TypeChecker_Env.trivial_guard)
                         | uu____9833 ->
                             let uu____9850 =
                               let uu____9883 =
                                 let uu____9894 =
                                   FStar_All.pipe_right neg_branch_conds
                                     (FStar_List.splitAt
                                        ((FStar_List.length lcases) -
                                           Prims.int_one))
                                    in
                                 FStar_All.pipe_right uu____9894
                                   (fun uu____9966  ->
                                      match uu____9966 with
                                      | (l1,l2) ->
                                          let uu____10007 = FStar_List.hd l2
                                             in
                                          (l1, uu____10007))
                                  in
                               match uu____9883 with
                               | (neg_branch_conds1,neg_last) ->
                                   let uu____10064 =
                                     let uu____10103 =
                                       FStar_All.pipe_right lcases
                                         (FStar_List.splitAt
                                            ((FStar_List.length lcases) -
                                               Prims.int_one))
                                        in
                                     FStar_All.pipe_right uu____10103
                                       (fun uu____10315  ->
                                          match uu____10315 with
                                          | (l1,l2) ->
                                              let uu____10466 =
                                                FStar_List.hd l2  in
                                              (l1, uu____10466))
                                      in
                                   (match uu____10064 with
                                    | (lcases1,(g_last,eff_last,uu____10568,c_last))
                                        ->
                                        let uu____10638 =
                                          let lc =
                                            maybe_return eff_last c_last  in
                                          let uu____10644 =
                                            FStar_TypeChecker_Common.lcomp_comp
                                              lc
                                             in
                                          match uu____10644 with
                                          | (c,g) ->
                                              let uu____10655 =
                                                let uu____10656 =
                                                  FStar_Syntax_Util.mk_conj
                                                    g_last neg_last
                                                   in
                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                  g uu____10656
                                                 in
                                              (c, uu____10655)
                                           in
                                        (match uu____10638 with
                                         | (c,g) ->
                                             let uu____10691 =
                                               let uu____10692 =
                                                 FStar_All.pipe_right
                                                   eff_last
                                                   (FStar_TypeChecker_Env.norm_eff_name
                                                      env)
                                                  in
                                               FStar_All.pipe_right
                                                 uu____10692
                                                 (FStar_TypeChecker_Env.get_effect_decl
                                                    env)
                                                in
                                             (lcases1, neg_branch_conds1,
                                               uu____10691, c, g)))
                                in
                             (match uu____9850 with
                              | (lcases1,neg_branch_conds1,md,comp,g_comp) ->
                                  FStar_List.fold_right2
                                    (fun uu____10824  ->
                                       fun neg_cond  ->
                                         fun uu____10826  ->
                                           match (uu____10824, uu____10826)
                                           with
                                           | ((g,eff_label,uu____10886,cthen),
                                              (uu____10888,celse,g_comp1)) ->
                                               let uu____10935 =
                                                 let uu____10940 =
                                                   maybe_return eff_label
                                                     cthen
                                                    in
                                                 FStar_TypeChecker_Common.lcomp_comp
                                                   uu____10940
                                                  in
                                               (match uu____10935 with
                                                | (cthen1,g_then) ->
                                                    let uu____10951 =
                                                      let uu____10962 =
                                                        lift_comps_sep_guards
                                                          env cthen1 celse
                                                          FStar_Pervasives_Native.None
                                                          false
                                                         in
                                                      match uu____10962 with
                                                      | (m,cthen2,celse1,g_lift_then,g_lift_else)
                                                          ->
                                                          let md1 =
                                                            FStar_TypeChecker_Env.get_effect_decl
                                                              env m
                                                             in
                                                          let uu____10990 =
                                                            FStar_All.pipe_right
                                                              cthen2
                                                              FStar_Syntax_Util.comp_to_comp_typ
                                                             in
                                                          let uu____10991 =
                                                            FStar_All.pipe_right
                                                              celse1
                                                              FStar_Syntax_Util.comp_to_comp_typ
                                                             in
                                                          (md1, uu____10990,
                                                            uu____10991,
                                                            g_lift_then,
                                                            g_lift_else)
                                                       in
                                                    (match uu____10951 with
                                                     | (md1,ct_then,ct_else,g_lift_then,g_lift_else)
                                                         ->
                                                         let fn =
                                                           let uu____11042 =
                                                             FStar_All.pipe_right
                                                               md1
                                                               FStar_Syntax_Util.is_layered
                                                              in
                                                           if uu____11042
                                                           then
                                                             mk_layered_conjunction
                                                           else
                                                             mk_non_layered_conjunction
                                                            in
                                                         let uu____11076 =
                                                           let uu____11081 =
                                                             FStar_TypeChecker_Env.get_range
                                                               env
                                                              in
                                                           fn env md1 u_res_t
                                                             res_t g ct_then
                                                             ct_else
                                                             uu____11081
                                                            in
                                                         (match uu____11076
                                                          with
                                                          | (c,g_conjunction)
                                                              ->
                                                              let g_then1 =
                                                                let uu____11093
                                                                  =
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_then
                                                                    g_lift_then
                                                                   in
                                                                let uu____11094
                                                                  =
                                                                  FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    g
                                                                   in
                                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                                  uu____11093
                                                                  uu____11094
                                                                 in
                                                              let g_else =
                                                                let uu____11096
                                                                  =
                                                                  let uu____11097
                                                                    =
                                                                    FStar_Syntax_Util.mk_neg
                                                                    g  in
                                                                  FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    uu____11097
                                                                   in
                                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                                  g_lift_else
                                                                  uu____11096
                                                                 in
                                                              let uu____11100
                                                                =
                                                                FStar_TypeChecker_Env.conj_guards
                                                                  [g_comp1;
                                                                  g_then1;
                                                                  g_else;
                                                                  g_conjunction]
                                                                 in
                                                              ((FStar_Pervasives_Native.Some
                                                                  md1), c,
                                                                uu____11100)))))
                                    lcases1 neg_branch_conds1
                                    ((FStar_Pervasives_Native.Some md), comp,
                                      g_comp))
                          in
                       (match uu____9799 with
                        | (md,comp,g_comp) ->
                            let uu____11116 =
                              let uu____11121 =
                                let check =
                                  FStar_Syntax_Util.mk_imp
                                    exhaustiveness_branch_cond
                                    FStar_Syntax_Util.t_false
                                   in
                                let check1 =
                                  let uu____11128 =
                                    FStar_TypeChecker_Env.get_range env  in
                                  label
                                    FStar_TypeChecker_Err.exhaustiveness_check
                                    uu____11128 check
                                   in
                                strengthen_comp env
                                  FStar_Pervasives_Native.None comp check1
                                  bind_cases_flags
                                 in
                              match uu____11121 with
                              | (c,g) ->
                                  let uu____11139 =
                                    FStar_TypeChecker_Env.conj_guard g_comp g
                                     in
                                  (c, uu____11139)
                               in
                            (match uu____11116 with
                             | (comp1,g_comp1) ->
                                 let g_comp2 =
                                   let uu____11147 =
                                     let uu____11148 =
                                       FStar_All.pipe_right scrutinee
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     [uu____11148]  in
                                   FStar_TypeChecker_Env.close_guard env0
                                     uu____11147 g_comp1
                                    in
                                 (match lcases with
                                  | [] -> (comp1, g_comp2)
                                  | uu____11191::[] -> (comp1, g_comp2)
                                  | uu____11234 ->
                                      let uu____11251 =
                                        let uu____11253 =
                                          FStar_All.pipe_right md
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____11253
                                          FStar_Syntax_Util.is_layered
                                         in
                                      if uu____11251
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
                                         let uu____11266 =
                                           destruct_wp_comp comp2  in
                                         match uu____11266 with
                                         | (uu____11277,uu____11278,wp) ->
                                             let ite_wp =
                                               let uu____11281 =
                                                 FStar_All.pipe_right md1
                                                   FStar_Syntax_Util.get_wp_ite_combinator
                                                  in
                                               FStar_All.pipe_right
                                                 uu____11281 FStar_Util.must
                                                in
                                             let wp1 =
                                               let uu____11289 =
                                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                                   [u_res_t] env md1 ite_wp
                                                  in
                                               let uu____11290 =
                                                 let uu____11291 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     res_t
                                                    in
                                                 let uu____11300 =
                                                   let uu____11311 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp
                                                      in
                                                   [uu____11311]  in
                                                 uu____11291 :: uu____11300
                                                  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu____11289 uu____11290
                                                 wp.FStar_Syntax_Syntax.pos
                                                in
                                             let uu____11344 =
                                               mk_comp md1 u_res_t res_t wp1
                                                 bind_cases_flags
                                                in
                                             (uu____11344, g_comp2))))))
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
          let uu____11379 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____11379 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____11395 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____11401 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____11395 uu____11401
              else
                (let uu____11410 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____11416 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____11410 uu____11416)
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
          let uu____11441 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____11441
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____11444 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____11444
        then u_res
        else
          (let is_total =
             let uu____11451 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____11451
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____11462 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____11462 with
              | FStar_Pervasives_Native.None  ->
                  let uu____11465 =
                    let uu____11471 =
                      let uu____11473 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____11473
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____11471)
                     in
                  FStar_Errors.raise_error uu____11465
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
      let uu____11497 = destruct_wp_comp ct  in
      match uu____11497 with
      | (u_t,t,wp) ->
          let vc =
            let uu____11514 =
              let uu____11515 =
                let uu____11516 =
                  FStar_All.pipe_right md
                    FStar_Syntax_Util.get_wp_trivial_combinator
                   in
                FStar_All.pipe_right uu____11516 FStar_Util.must  in
              FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                uu____11515
               in
            let uu____11523 =
              let uu____11524 = FStar_Syntax_Syntax.as_arg t  in
              let uu____11533 =
                let uu____11544 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____11544]  in
              uu____11524 :: uu____11533  in
            let uu____11577 = FStar_TypeChecker_Env.get_range env  in
            FStar_Syntax_Syntax.mk_Tm_app uu____11514 uu____11523 uu____11577
             in
          let uu____11578 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____11578)
  
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
                  let uu____11633 =
                    FStar_TypeChecker_Env.try_lookup_lid env f  in
                  match uu____11633 with
                  | FStar_Pervasives_Native.Some uu____11648 ->
                      ((let uu____11666 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____11666
                        then
                          let uu____11670 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____11670
                        else ());
                       (let coercion =
                          let uu____11676 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____11676
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____11683 =
                            let uu____11684 =
                              let uu____11685 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____11685
                               in
                            (FStar_Pervasives_Native.None, uu____11684)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____11683
                           in
                        let e1 =
                          let uu____11689 =
                            let uu____11690 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____11690]  in
                          FStar_Syntax_Syntax.mk_Tm_app coercion2 uu____11689
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____11724 =
                          let uu____11730 =
                            let uu____11732 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____11732
                             in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____11730)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____11724);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____11751 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____11769 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____11780 -> false 
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
      let uu____11804 = FStar_Syntax_Util.head_and_args t2  in
      match uu____11804 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____11849 =
              let uu____11864 =
                let uu____11865 = FStar_Syntax_Subst.compress h1  in
                uu____11865.FStar_Syntax_Syntax.n  in
              (uu____11864, args)  in
            match uu____11849 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____11912,uu____11913) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____11946) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match
               (uu____11967,branches),uu____11969) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc  ->
                        fun br  ->
                          match acc with
                          | Yes uu____12033 -> Maybe
                          | Maybe  -> Maybe
                          | No  ->
                              let uu____12034 =
                                FStar_Syntax_Subst.open_branch br  in
                              (match uu____12034 with
                               | (uu____12035,uu____12036,br_body) ->
                                   let uu____12054 =
                                     let uu____12055 =
                                       let uu____12060 =
                                         let uu____12061 =
                                           let uu____12064 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names
                                              in
                                           FStar_All.pipe_right uu____12064
                                             FStar_Util.set_elements
                                            in
                                         FStar_All.pipe_right uu____12061
                                           (FStar_TypeChecker_Env.push_bvs
                                              env)
                                          in
                                       check_erased uu____12060  in
                                     FStar_All.pipe_right br_body uu____12055
                                      in
                                   (match uu____12054 with
                                    | No  -> No
                                    | uu____12075 -> Maybe))) No)
            | uu____12076 -> No  in
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
            (((let uu____12128 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____12128) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____12147 =
                 let uu____12148 = FStar_Syntax_Subst.compress t1  in
                 uu____12148.FStar_Syntax_Syntax.n  in
               match uu____12147 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____12153 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____12163 =
                 let uu____12164 = FStar_Syntax_Subst.compress t1  in
                 uu____12164.FStar_Syntax_Syntax.n  in
               match uu____12163 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____12169 -> false  in
             let is_type t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let t2 = FStar_Syntax_Util.unrefine t1  in
               let uu____12180 =
                 let uu____12181 = FStar_Syntax_Subst.compress t2  in
                 uu____12181.FStar_Syntax_Syntax.n  in
               match uu____12180 with
               | FStar_Syntax_Syntax.Tm_type uu____12185 -> true
               | uu____12187 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____12190 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____12190 with
             | (head,args) ->
                 ((let uu____12240 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____12240
                   then
                     let uu____12244 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____12246 = FStar_Syntax_Print.term_to_string e
                        in
                     let uu____12248 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____12250 =
                       FStar_Syntax_Print.term_to_string exp_t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____12244 uu____12246 uu____12248 uu____12250
                   else ());
                  (let mk_erased u t =
                     let uu____12268 =
                       let uu____12271 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____12271 [u]  in
                     let uu____12272 =
                       let uu____12283 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____12283]  in
                     FStar_Syntax_Util.mk_app uu____12268 uu____12272  in
                   let uu____12308 =
                     let uu____12323 =
                       let uu____12324 = FStar_Syntax_Util.un_uinst head  in
                       uu____12324.FStar_Syntax_Syntax.n  in
                     (uu____12323, args)  in
                   match uu____12308 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type exp_t)
                       ->
                       let uu____12362 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____12362 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____12402 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____12402 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____12442 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____12442 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____12482 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____12482 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____12503 ->
                       let uu____12518 =
                         let uu____12523 = check_erased env res_typ  in
                         let uu____12524 = check_erased env exp_t  in
                         (uu____12523, uu____12524)  in
                       (match uu____12518 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____12533 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____12533 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____12544 =
                                   let uu____12549 =
                                     let uu____12550 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____12550]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____12549
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____12544 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____12585 =
                              let uu____12590 =
                                let uu____12591 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____12591]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____12590
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____12585 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____12624 ->
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
        let uu____12659 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____12659 with
        | (hd,args) ->
            let uu____12708 =
              let uu____12723 =
                let uu____12724 = FStar_Syntax_Subst.compress hd  in
                uu____12724.FStar_Syntax_Syntax.n  in
              (uu____12723, args)  in
            (match uu____12708 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____12762 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun uu____12789  ->
                      FStar_Pervasives_Native.Some uu____12789) uu____12762
             | uu____12790 -> FStar_Pervasives_Native.None)
  
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
          (let uu____12843 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____12843
           then
             let uu____12846 = FStar_Syntax_Print.term_to_string e  in
             let uu____12848 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____12850 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____12846 uu____12848 uu____12850
           else ());
          (let use_eq =
             (env.FStar_TypeChecker_Env.use_eq_strict ||
                env.FStar_TypeChecker_Env.use_eq)
               ||
               (let uu____12860 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____12860 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____12885 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____12911 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____12911, false)
             else
               (let uu____12921 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____12921, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____12934) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____12946 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____12946
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1444_12962 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1444_12962.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1444_12962.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1444_12962.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard) ->
               let uu____12969 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____12969 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____12985 =
                      let uu____12986 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____12986 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____13006 =
                            let uu____13008 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____13008 = FStar_Syntax_Util.Equal  in
                          if uu____13006
                          then
                            ((let uu____13015 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____13015
                              then
                                let uu____13019 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____13021 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____13019 uu____13021
                              else ());
                             (let uu____13026 = set_result_typ c  in
                              (uu____13026, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____13033 ->
                                   true
                               | uu____13041 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____13050 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____13050
                                  in
                               let lc1 =
                                 let uu____13052 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____13053 =
                                   let uu____13054 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____13054)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____13052 uu____13053
                                  in
                               ((let uu____13058 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____13058
                                 then
                                   let uu____13062 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____13064 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____13066 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____13068 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____13062 uu____13064 uu____13066
                                     uu____13068
                                 else ());
                                (let uu____13073 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____13073 with
                                 | (c1,g_lc) ->
                                     let uu____13084 = set_result_typ c1  in
                                     let uu____13085 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____13084, uu____13085)))
                             else
                               ((let uu____13089 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____13089
                                 then
                                   let uu____13093 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____13095 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____13093 uu____13095
                                 else ());
                                (let uu____13100 = set_result_typ c  in
                                 (uu____13100, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1481_13104 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred_to_tac =
                          (uu___1481_13104.FStar_TypeChecker_Common.deferred_to_tac);
                        FStar_TypeChecker_Common.deferred =
                          (uu___1481_13104.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1481_13104.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1481_13104.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____13114 =
                      let uu____13115 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____13115
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____13125 =
                           let uu____13126 = FStar_Syntax_Subst.compress f1
                              in
                           uu____13126.FStar_Syntax_Syntax.n  in
                         match uu____13125 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____13133,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____13135;
                                            FStar_Syntax_Syntax.vars =
                                              uu____13136;_},uu____13137)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1497_13163 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1497_13163.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1497_13163.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1497_13163.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____13164 ->
                             let uu____13165 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____13165 with
                              | (c,g_c) ->
                                  ((let uu____13177 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____13177
                                    then
                                      let uu____13181 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____13183 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____13185 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____13187 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____13181 uu____13183 uu____13185
                                        uu____13187
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
                                        let uu____13200 =
                                          let uu____13201 =
                                            FStar_Syntax_Syntax.as_arg xexp
                                             in
                                          [uu____13201]  in
                                        FStar_Syntax_Syntax.mk_Tm_app f1
                                          uu____13200
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____13228 =
                                      let uu____13233 =
                                        FStar_All.pipe_left
                                          (fun uu____13254  ->
                                             FStar_Pervasives_Native.Some
                                               uu____13254)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____13255 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____13256 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____13257 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____13233
                                        uu____13255 e uu____13256 uu____13257
                                       in
                                    match uu____13228 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1515_13265 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1515_13265.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1515_13265.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____13267 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____13267
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____13270 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____13270 with
                                         | (c2,g_lc) ->
                                             ((let uu____13282 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____13282
                                               then
                                                 let uu____13286 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____13286
                                               else ());
                                              (let uu____13291 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____13291))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_13300  ->
                              match uu___6_13300 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____13303 -> []))
                       in
                    let lc1 =
                      let uu____13305 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____13305 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1531_13307 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred_to_tac =
                          (uu___1531_13307.FStar_TypeChecker_Common.deferred_to_tac);
                        FStar_TypeChecker_Common.deferred =
                          (uu___1531_13307.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1531_13307.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1531_13307.FStar_TypeChecker_Common.implicits)
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
        let uu____13343 =
          let uu____13346 =
            let uu____13347 =
              let uu____13356 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_Syntax_Syntax.as_arg uu____13356  in
            [uu____13347]  in
          FStar_Syntax_Syntax.mk_Tm_app ens uu____13346
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____13343  in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____13379 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____13379
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____13398 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____13414 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____13431 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____13431
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____13447)::(ens,uu____13449)::uu____13450 ->
                    let uu____13493 =
                      let uu____13496 = norm req  in
                      FStar_Pervasives_Native.Some uu____13496  in
                    let uu____13497 =
                      let uu____13498 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm uu____13498  in
                    (uu____13493, uu____13497)
                | uu____13501 ->
                    let uu____13512 =
                      let uu____13518 =
                        let uu____13520 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____13520
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____13518)
                       in
                    FStar_Errors.raise_error uu____13512
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____13540)::uu____13541 ->
                    let uu____13568 =
                      let uu____13573 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____13573
                       in
                    (match uu____13568 with
                     | (us_r,uu____13605) ->
                         let uu____13606 =
                           let uu____13611 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____13611
                            in
                         (match uu____13606 with
                          | (us_e,uu____13643) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____13646 =
                                  let uu____13647 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____13647
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____13646
                                  us_r
                                 in
                              let as_ens =
                                let uu____13649 =
                                  let uu____13650 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____13650
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____13649
                                  us_e
                                 in
                              let req =
                                let uu____13652 =
                                  let uu____13653 =
                                    let uu____13664 =
                                      FStar_Syntax_Syntax.as_arg wp  in
                                    [uu____13664]  in
                                  ((ct1.FStar_Syntax_Syntax.result_typ),
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.imp_tag))
                                    :: uu____13653
                                   in
                                FStar_Syntax_Syntax.mk_Tm_app as_req
                                  uu____13652
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____13702 =
                                  let uu____13703 =
                                    let uu____13714 =
                                      FStar_Syntax_Syntax.as_arg wp  in
                                    [uu____13714]  in
                                  ((ct1.FStar_Syntax_Syntax.result_typ),
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.imp_tag))
                                    :: uu____13703
                                   in
                                FStar_Syntax_Syntax.mk_Tm_app as_ens
                                  uu____13702
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____13751 =
                                let uu____13754 = norm req  in
                                FStar_Pervasives_Native.Some uu____13754  in
                              let uu____13755 =
                                let uu____13756 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm uu____13756  in
                              (uu____13751, uu____13755)))
                | uu____13759 -> failwith "Impossible"))
  
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
        (let uu____13798 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____13798
         then
           let uu____13803 = FStar_Syntax_Print.term_to_string tm  in
           let uu____13805 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____13803
             uu____13805
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
          (let uu____13864 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____13864
           then
             let uu____13869 = FStar_Syntax_Print.term_to_string tm  in
             let uu____13871 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____13869
               uu____13871
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____13882 =
      let uu____13884 =
        let uu____13885 = FStar_Syntax_Subst.compress t  in
        uu____13885.FStar_Syntax_Syntax.n  in
      match uu____13884 with
      | FStar_Syntax_Syntax.Tm_app uu____13889 -> false
      | uu____13907 -> true  in
    if uu____13882
    then t
    else
      (let uu____13912 = FStar_Syntax_Util.head_and_args t  in
       match uu____13912 with
       | (head,args) ->
           let uu____13955 =
             let uu____13957 =
               let uu____13958 = FStar_Syntax_Subst.compress head  in
               uu____13958.FStar_Syntax_Syntax.n  in
             match uu____13957 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____13963 -> false  in
           if uu____13955
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____13995 ->
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
          ((let uu____14042 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____14042
            then
              let uu____14045 = FStar_Syntax_Print.term_to_string e  in
              let uu____14047 = FStar_Syntax_Print.term_to_string t  in
              let uu____14049 =
                let uu____14051 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____14051
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____14045 uu____14047 uu____14049
            else ());
           (let unfolded_arrow_formals t1 =
              let rec aux bs t2 =
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf env t2  in
                let uu____14087 = FStar_Syntax_Util.arrow_formals t3  in
                match uu____14087 with
                | (bs',t4) ->
                    (match bs' with
                     | [] -> bs
                     | bs'1 -> aux (FStar_List.append bs bs'1) t4)
                 in
              aux [] t1  in
            let number_of_implicits t1 =
              let formals = unfolded_arrow_formals t1  in
              let n_implicits =
                let uu____14121 =
                  FStar_All.pipe_right formals
                    (FStar_Util.prefix_until
                       (fun uu____14199  ->
                          match uu____14199 with
                          | (uu____14207,imp) ->
                              (FStar_Option.isNone imp) ||
                                (let uu____14214 =
                                   FStar_Syntax_Util.eq_aqual imp
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Equality)
                                    in
                                 uu____14214 = FStar_Syntax_Util.Equal)))
                   in
                match uu____14121 with
                | FStar_Pervasives_Native.None  -> FStar_List.length formals
                | FStar_Pervasives_Native.Some
                    (implicits,_first_explicit,_rest) ->
                    FStar_List.length implicits
                 in
              n_implicits  in
            let inst_n_binders t1 =
              let uu____14333 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____14333 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____14347 =
                      let uu____14353 =
                        let uu____14355 = FStar_Util.string_of_int n_expected
                           in
                        let uu____14357 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____14359 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____14355 uu____14357 uu____14359
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____14353)
                       in
                    let uu____14363 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____14347 uu____14363
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_14381 =
              match uu___7_14381 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____14424 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____14424 with
                 | (bs1,c1) ->
                     let rec aux subst inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some
                          uu____14555,uu____14542) when
                           uu____14555 = Prims.int_zero ->
                           ([], bs2, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____14588,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____14590))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____14624 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____14624 with
                            | (v,uu____14665,g) ->
                                ((let uu____14680 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____14680
                                  then
                                    let uu____14683 =
                                      FStar_Syntax_Print.term_to_string v  in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____14683
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst
                                     in
                                  let uu____14693 =
                                    aux subst1 (decr_inst inst_n) rest  in
                                  match uu____14693 with
                                  | (args,bs3,subst2,g') ->
                                      let uu____14786 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____14786))))
                       | (uu____14813,(x,FStar_Pervasives_Native.Some
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
                                 let uu____14852 =
                                   let uu____14859 = FStar_Dyn.mkdyn env  in
                                   (uu____14859, tau)  in
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   uu____14852
                             | FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                 attr ->
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_attr attr
                              in
                           let uu____14865 =
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict
                               (FStar_Pervasives_Native.Some meta_t)
                              in
                           (match uu____14865 with
                            | (v,uu____14906,g) ->
                                ((let uu____14921 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____14921
                                  then
                                    let uu____14924 =
                                      FStar_Syntax_Print.term_to_string v  in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____14924
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst
                                     in
                                  let uu____14934 =
                                    aux subst1 (decr_inst inst_n) rest  in
                                  match uu____14934 with
                                  | (args,bs3,subst2,g') ->
                                      let uu____15027 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____15027))))
                       | (uu____15054,bs3) ->
                           ([], bs3, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____15102 =
                       let uu____15129 = inst_n_binders t1  in
                       aux [] uu____15129 bs1  in
                     (match uu____15102 with
                      | (args,bs2,subst,guard) ->
                          (match (args, bs2) with
                           | ([],uu____15201) -> (e, torig, guard)
                           | (uu____15232,[]) when
                               let uu____15263 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____15263 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____15265 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____15293 ->
                                     FStar_Syntax_Util.arrow bs2 c1
                                  in
                               let t3 = FStar_Syntax_Subst.subst subst t2  in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               (e1, t3, guard))))
            | uu____15304 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs  ->
    let uu____15316 =
      let uu____15320 = FStar_Util.set_elements univs  in
      FStar_All.pipe_right uu____15320
        (FStar_List.map
           (fun u  ->
              let uu____15332 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____15332 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____15316 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____15360 = FStar_Util.set_is_empty x  in
      if uu____15360
      then []
      else
        (let s =
           let uu____15380 =
             let uu____15383 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____15383  in
           FStar_All.pipe_right uu____15380 FStar_Util.set_elements  in
         (let uu____15401 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____15401
          then
            let uu____15406 =
              let uu____15408 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____15408  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____15406
          else ());
         (let r =
            let uu____15417 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____15417  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____15462 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____15462
                     then
                       let uu____15467 =
                         let uu____15469 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____15469
                          in
                       let uu____15473 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____15475 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____15467 uu____15473 uu____15475
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
        let uu____15505 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____15505 FStar_Util.set_elements  in
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
        | ([],uu____15544) -> generalized_univ_names
        | (uu____15551,[]) -> explicit_univ_names
        | uu____15558 ->
            let uu____15567 =
              let uu____15573 =
                let uu____15575 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____15575
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____15573)
               in
            FStar_Errors.raise_error uu____15567 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____15597 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____15597
       then
         let uu____15602 = FStar_Syntax_Print.term_to_string t  in
         let uu____15604 = FStar_Syntax_Print.univ_names_to_string univnames
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____15602 uu____15604
       else ());
      (let univs = FStar_Syntax_Free.univs t  in
       (let uu____15613 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____15613
        then
          let uu____15618 = string_of_univs univs  in
          FStar_Util.print1 "univs to gen : %s\n" uu____15618
        else ());
       (let gen = gen_univs env univs  in
        (let uu____15627 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____15627
         then
           let uu____15632 = FStar_Syntax_Print.term_to_string t  in
           let uu____15634 = FStar_Syntax_Print.univ_names_to_string gen  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____15632 uu____15634
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
        let uu____15718 =
          let uu____15720 =
            FStar_Util.for_all
              (fun uu____15734  ->
                 match uu____15734 with
                 | (uu____15744,uu____15745,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____15720  in
        if uu____15718
        then FStar_Pervasives_Native.None
        else
          (let norm c =
             (let uu____15797 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____15797
              then
                let uu____15800 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____15800
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____15807 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____15807
               then
                 let uu____15810 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____15810
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____15828 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____15828 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____15862 =
             match uu____15862 with
             | (lbname,e,c) ->
                 let c1 = norm c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____15899 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____15899
                   then
                     let uu____15904 =
                       let uu____15906 =
                         let uu____15910 = FStar_Util.set_elements univs  in
                         FStar_All.pipe_right uu____15910
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____15906
                         (FStar_String.concat ", ")
                        in
                     let uu____15966 =
                       let uu____15968 =
                         let uu____15972 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____15972
                           (FStar_List.map
                              (fun u  ->
                                 let uu____15985 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____15987 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____15985
                                   uu____15987))
                          in
                       FStar_All.pipe_right uu____15968
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____15904
                       uu____15966
                   else ());
                  (let univs1 =
                     let uu____16001 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs1  ->
                          fun uv  ->
                            let uu____16013 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs1 uu____16013) univs
                       uu____16001
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____16020 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____16020
                    then
                      let uu____16025 =
                        let uu____16027 =
                          let uu____16031 = FStar_Util.set_elements univs1
                             in
                          FStar_All.pipe_right uu____16031
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____16027
                          (FStar_String.concat ", ")
                         in
                      let uu____16087 =
                        let uu____16089 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____16103 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____16105 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____16103
                                    uu____16105))
                           in
                        FStar_All.pipe_right uu____16089
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____16025 uu____16087
                    else ());
                   (univs1, uvs, (lbname, e, c1))))
              in
           let uu____16126 =
             let uu____16143 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____16143  in
           match uu____16126 with
           | (univs,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____16233 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____16233
                 then ()
                 else
                   (let uu____16238 = lec_hd  in
                    match uu____16238 with
                    | (lb1,uu____16246,uu____16247) ->
                        let uu____16248 = lec2  in
                        (match uu____16248 with
                         | (lb2,uu____16256,uu____16257) ->
                             let msg =
                               let uu____16260 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____16262 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____16260 uu____16262
                                in
                             let uu____16265 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____16265))
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
                 let uu____16333 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____16333
                 then ()
                 else
                   (let uu____16338 = lec_hd  in
                    match uu____16338 with
                    | (lb1,uu____16346,uu____16347) ->
                        let uu____16348 = lec2  in
                        (match uu____16348 with
                         | (lb2,uu____16356,uu____16357) ->
                             let msg =
                               let uu____16360 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____16362 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____16360 uu____16362
                                in
                             let uu____16365 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____16365))
                  in
               let lecs1 =
                 let uu____16376 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____16429 = univs_and_uvars_of_lec this_lec  in
                        match uu____16429 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____16376 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail rng k =
                   let uu____16539 = lec_hd  in
                   match uu____16539 with
                   | (lbname,e,c) ->
                       let uu____16549 =
                         let uu____16555 =
                           let uu____16557 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____16559 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____16561 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____16557 uu____16559 uu____16561
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____16555)
                          in
                       FStar_Errors.raise_error uu____16549 rng
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____16583 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____16583 with
                         | FStar_Pervasives_Native.Some uu____16592 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____16600 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____16604 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____16604 with
                              | (bs,kres) ->
                                  ((let uu____16624 =
                                      let uu____16625 =
                                        let uu____16628 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____16628
                                         in
                                      uu____16625.FStar_Syntax_Syntax.n  in
                                    match uu____16624 with
                                    | FStar_Syntax_Syntax.Tm_type uu____16629
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____16633 =
                                          let uu____16635 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____16635  in
                                        if uu____16633
                                        then
                                          fail
                                            u.FStar_Syntax_Syntax.ctx_uvar_range
                                            kres
                                        else ()
                                    | uu____16640 ->
                                        fail
                                          u.FStar_Syntax_Syntax.ctx_uvar_range
                                          kres);
                                   (let a =
                                      let uu____16642 =
                                        let uu____16645 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun uu____16648  ->
                                             FStar_Pervasives_Native.Some
                                               uu____16648) uu____16645
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____16642
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____16656 ->
                                          let uu____16657 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____16657
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
                      (fun uu____16760  ->
                         match uu____16760 with
                         | (lbname,e,c) ->
                             let uu____16806 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____16867 ->
                                   let uu____16880 = (e, c)  in
                                   (match uu____16880 with
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
                                                (fun uu____16920  ->
                                                   match uu____16920 with
                                                   | (x,uu____16926) ->
                                                       let uu____16927 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____16927)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____16945 =
                                                let uu____16947 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____16947
                                                 in
                                              if uu____16945
                                              then
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  tm tvar_args
                                                  tm.FStar_Syntax_Syntax.pos
                                              else tm  in
                                            FStar_Syntax_InstFV.inst
                                              instantiate_lbname_with_app e1
                                          else e1  in
                                        let t =
                                          let uu____16956 =
                                            let uu____16957 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____16957.FStar_Syntax_Syntax.n
                                             in
                                          match uu____16956 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____16982 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____16982 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____16993 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____16997 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____16997, gen_tvars))
                                in
                             (match uu____16806 with
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
        (let uu____17144 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____17144
         then
           let uu____17147 =
             let uu____17149 =
               FStar_List.map
                 (fun uu____17164  ->
                    match uu____17164 with
                    | (lb,uu____17173,uu____17174) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____17149 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____17147
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____17200  ->
                match uu____17200 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____17229 = gen env is_rec lecs  in
           match uu____17229 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____17328  ->
                       match uu____17328 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____17390 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____17390
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____17438  ->
                           match uu____17438 with
                           | (l,us,e,c,gvs) ->
                               let uu____17472 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____17474 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____17476 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____17478 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____17480 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____17472 uu____17474 uu____17476
                                 uu____17478 uu____17480))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames  ->
              fun uu____17525  ->
                match uu____17525 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____17569 =
                      check_universe_generalization univnames
                        generalized_univs t
                       in
                    (l, uu____17569, t, c, gvs)) univnames_lecs
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
        let uu____17624 =
          let uu____17628 =
            let uu____17630 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____17630  in
          FStar_Pervasives_Native.Some uu____17628  in
        FStar_Profiling.profile
          (fun uu____17647  -> generalize' env is_rec lecs) uu____17624
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
              let uu____17704 =
                FStar_TypeChecker_Rel.get_teq_predicate env2 t1 t21  in
              match uu____17704 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some f ->
                  let uu____17710 = FStar_TypeChecker_Env.apply_guard f e  in
                  FStar_All.pipe_right uu____17710
                    (fun uu____17713  ->
                       FStar_Pervasives_Native.Some uu____17713)
            else
              if env2.FStar_TypeChecker_Env.use_eq
              then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
              else
                (let uu____17722 =
                   FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                    in
                 match uu____17722 with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some f ->
                     let uu____17728 = FStar_TypeChecker_Env.apply_guard f e
                        in
                     FStar_All.pipe_left
                       (fun uu____17731  ->
                          FStar_Pervasives_Native.Some uu____17731)
                       uu____17728)
             in
          let uu____17732 = maybe_coerce_lc env1 e lc t2  in
          match uu____17732 with
          | (e1,lc1,g_c) ->
              let uu____17748 =
                check env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____17748 with
               | FStar_Pervasives_Native.None  ->
                   let uu____17757 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____17763 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____17757 uu____17763
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____17772 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____17772
                     then
                       let uu____17777 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____17777
                     else ());
                    (let uu____17783 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (e1, lc1, uu____17783))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____17811 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____17811
         then
           let uu____17814 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____17814
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____17828 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____17828 with
         | (c,g_c) ->
             let uu____17840 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____17840
             then
               let uu____17848 =
                 let uu____17850 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____17850  in
               (uu____17848, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____17858 =
                    let uu____17859 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____17859
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____17858
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____17860 = check_trivial_precondition env c1  in
                match uu____17860 with
                | (ct,vc,g_pre) ->
                    ((let uu____17876 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____17876
                      then
                        let uu____17881 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____17881
                      else ());
                     (let uu____17886 =
                        let uu____17888 =
                          let uu____17889 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____17889  in
                        discharge uu____17888  in
                      let uu____17890 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____17886, uu____17890)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head  ->
    fun seen_args  ->
      let short_bin_op f uu___8_17924 =
        match uu___8_17924 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst,uu____17934)::[] -> f fst
        | uu____17959 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____17971 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____17971
          (fun uu____17972  ->
             FStar_TypeChecker_Common.NonTrivial uu____17972)
         in
      let op_or_e e =
        let uu____17983 =
          let uu____17984 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____17984  in
        FStar_All.pipe_right uu____17983
          (fun uu____17987  ->
             FStar_TypeChecker_Common.NonTrivial uu____17987)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun uu____17994  ->
             FStar_TypeChecker_Common.NonTrivial uu____17994)
         in
      let op_or_t t =
        let uu____18005 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____18005
          (fun uu____18008  ->
             FStar_TypeChecker_Common.NonTrivial uu____18008)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun uu____18015  ->
             FStar_TypeChecker_Common.NonTrivial uu____18015)
         in
      let short_op_ite uu___9_18021 =
        match uu___9_18021 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____18031)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____18058)::[] ->
            let uu____18099 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____18099
              (fun uu____18100  ->
                 FStar_TypeChecker_Common.NonTrivial uu____18100)
        | uu____18101 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____18113 =
          let uu____18121 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____18121)  in
        let uu____18129 =
          let uu____18139 =
            let uu____18147 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____18147)  in
          let uu____18155 =
            let uu____18165 =
              let uu____18173 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____18173)  in
            let uu____18181 =
              let uu____18191 =
                let uu____18199 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____18199)  in
              let uu____18207 =
                let uu____18217 =
                  let uu____18225 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____18225)  in
                [uu____18217; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____18191 :: uu____18207  in
            uu____18165 :: uu____18181  in
          uu____18139 :: uu____18155  in
        uu____18113 :: uu____18129  in
      match head.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____18287 =
            FStar_Util.find_map table
              (fun uu____18302  ->
                 match uu____18302 with
                 | (x,mk) ->
                     let uu____18319 = FStar_Ident.lid_equals x lid  in
                     if uu____18319
                     then
                       let uu____18324 = mk seen_args  in
                       FStar_Pervasives_Native.Some uu____18324
                     else FStar_Pervasives_Native.None)
             in
          (match uu____18287 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____18328 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____18336 =
      let uu____18337 = FStar_Syntax_Util.un_uinst l  in
      uu____18337.FStar_Syntax_Syntax.n  in
    match uu____18336 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____18342 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd,uu____18378)::uu____18379 -> FStar_Syntax_Syntax.range_of_bv hd
        | uu____18398 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____18407,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____18408))::uu____18409 -> bs
      | uu____18427 ->
          let uu____18428 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____18428 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____18432 =
                 let uu____18433 = FStar_Syntax_Subst.compress t  in
                 uu____18433.FStar_Syntax_Syntax.n  in
               (match uu____18432 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____18437) ->
                    let uu____18458 =
                      FStar_Util.prefix_until
                        (fun uu___10_18498  ->
                           match uu___10_18498 with
                           | (uu____18506,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____18507)) ->
                               false
                           | uu____18512 -> true) bs'
                       in
                    (match uu____18458 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____18548,uu____18549) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____18621,uu____18622) ->
                         let uu____18695 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____18716  ->
                                   match uu____18716 with
                                   | (x,uu____18725) ->
                                       let uu____18730 =
                                         FStar_Ident.string_of_id
                                           x.FStar_Syntax_Syntax.ppname
                                          in
                                       FStar_Util.starts_with uu____18730 "'"))
                            in
                         if uu____18695
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____18776  ->
                                     match uu____18776 with
                                     | (x,i) ->
                                         let uu____18795 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____18795, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____18806 -> bs))
  
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
            let uu____18835 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____18835
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
          let uu____18866 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____18866
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
        (let uu____18909 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____18909
         then
           ((let uu____18914 = FStar_Ident.string_of_lid lident  in
             d uu____18914);
            (let uu____18916 = FStar_Ident.string_of_lid lident  in
             let uu____18918 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____18916 uu____18918))
         else ());
        (let fv =
           let uu____18924 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____18924
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
         let uu____18936 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Range.dummyRange
            in
         ((let uu___2158_18938 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2158_18938.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2158_18938.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2158_18938.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2158_18938.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2158_18938.FStar_Syntax_Syntax.sigopts)
           }), uu____18936))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_18956 =
        match uu___11_18956 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____18959 -> false  in
      let reducibility uu___12_18967 =
        match uu___12_18967 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____18974 -> false  in
      let assumption uu___13_18982 =
        match uu___13_18982 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____18986 -> false  in
      let reification uu___14_18994 =
        match uu___14_18994 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____18997 -> true
        | uu____18999 -> false  in
      let inferred uu___15_19007 =
        match uu___15_19007 with
        | FStar_Syntax_Syntax.Discriminator uu____19009 -> true
        | FStar_Syntax_Syntax.Projector uu____19011 -> true
        | FStar_Syntax_Syntax.RecordType uu____19017 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____19027 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____19040 -> false  in
      let has_eq uu___16_19048 =
        match uu___16_19048 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____19052 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____19131 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____19138 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____19171 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____19171))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____19202 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____19202
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
           | FStar_Syntax_Syntax.Sig_bundle uu____19222 ->
               let uu____19231 =
                 let uu____19233 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_19239  ->
                           match uu___17_19239 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____19242 -> false))
                    in
                 Prims.op_Negation uu____19233  in
               if uu____19231
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____19249 -> ()
           | FStar_Syntax_Syntax.Sig_fail uu____19256 -> ()
           | uu____19269 ->
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
      let uu____19283 =
        let uu____19285 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_19291  ->
                  match uu___18_19291 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____19294 -> false))
           in
        FStar_All.pipe_right uu____19285 Prims.op_Negation  in
      if uu____19283
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____19315 =
            let uu____19321 =
              let uu____19323 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____19323 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____19321)  in
          FStar_Errors.raise_error uu____19315 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____19341 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____19349 =
            let uu____19351 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____19351  in
          if uu____19349 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____19362),uu____19363) ->
              ((let uu____19375 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____19375
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____19384 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____19384
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____19395 ->
              ((let uu____19405 =
                  let uu____19407 =
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
                  Prims.op_Negation uu____19407  in
                if uu____19405 then err'1 () else ());
               (let uu____19417 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_19423  ->
                           match uu___19_19423 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____19426 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____19417
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____19432 ->
              let uu____19439 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____19439 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____19447 ->
              let uu____19454 =
                let uu____19456 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____19456  in
              if uu____19454 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____19466 ->
              let uu____19467 =
                let uu____19469 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____19469  in
              if uu____19467 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19479 ->
              let uu____19492 =
                let uu____19494 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____19494  in
              if uu____19492 then err'1 () else ()
          | uu____19504 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____19543 =
          let uu____19544 = FStar_Syntax_Subst.compress t1  in
          uu____19544.FStar_Syntax_Syntax.n  in
        match uu____19543 with
        | FStar_Syntax_Syntax.Tm_arrow uu____19548 ->
            let uu____19563 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____19563 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____19572;
               FStar_Syntax_Syntax.index = uu____19573;
               FStar_Syntax_Syntax.sort = t2;_},uu____19575)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head,uu____19584) -> descend env head
        | FStar_Syntax_Syntax.Tm_uinst (head,uu____19610) -> descend env head
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____19616 -> false
      
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
        (let uu____19626 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____19626
         then
           let uu____19631 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____19631
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
                  let uu____19696 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____19696 r  in
                let uu____19706 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____19706 with
                | (uu____19715,signature) ->
                    let uu____19717 =
                      let uu____19718 = FStar_Syntax_Subst.compress signature
                         in
                      uu____19718.FStar_Syntax_Syntax.n  in
                    (match uu____19717 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____19726) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____19774 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____19790 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____19792 =
                                       FStar_Ident.string_of_lid eff_name  in
                                     let uu____19794 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____19790 uu____19792 uu____19794) r
                                 in
                              (match uu____19774 with
                               | (is,g) ->
                                   let uu____19807 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____19809 =
                                             let uu____19810 =
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
                                                 = uu____19810;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____19809
                                            in
                                         let uu____19829 =
                                           let uu____19830 =
                                             let uu____19845 =
                                               let uu____19854 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   FStar_Syntax_Syntax.t_unit
                                                  in
                                               [uu____19854]  in
                                             (uu____19845, eff_c)  in
                                           FStar_Syntax_Syntax.Tm_arrow
                                             uu____19830
                                            in
                                         FStar_Syntax_Syntax.mk uu____19829 r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____19885 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____19885
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____19894 =
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg (a_tm
                                             :: is)
                                            in
                                         FStar_Syntax_Syntax.mk_Tm_app repr
                                           uu____19894 r
                                      in
                                   (uu____19807, g))
                          | uu____19903 -> fail signature)
                     | uu____19904 -> fail signature)
  
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
            let uu____19935 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____19935
              (fun ed  ->
                 let uu____19943 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____19943 u a_tm)
  
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
              let uu____19979 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____19979 with
              | (uu____19984,sig_tm) ->
                  let fail t =
                    let uu____19992 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____19992 r  in
                  let uu____19998 =
                    let uu____19999 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____19999.FStar_Syntax_Syntax.n  in
                  (match uu____19998 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____20003) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____20026)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____20048 -> fail sig_tm)
                   | uu____20049 -> fail sig_tm)
  
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
          (let uu____20080 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____20080
           then
             let uu____20085 = FStar_Syntax_Print.comp_to_string c  in
             let uu____20087 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____20085 uu____20087
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let lift_name =
             let uu____20096 =
               FStar_Ident.string_of_lid ct.FStar_Syntax_Syntax.effect_name
                in
             let uu____20098 = FStar_Ident.string_of_lid tgt  in
             FStar_Util.format2 "%s ~> %s" uu____20096 uu____20098  in
           let uu____20101 =
             let uu____20112 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____20113 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____20112, (ct.FStar_Syntax_Syntax.result_typ), uu____20113)
              in
           match uu____20101 with
           | (u,a,c_is) ->
               let uu____20161 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____20161 with
                | (uu____20170,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____20181 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____20183 = FStar_Ident.string_of_lid tgt  in
                      let uu____20185 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____20181 uu____20183 s uu____20185
                       in
                    let uu____20188 =
                      let uu____20221 =
                        let uu____20222 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____20222.FStar_Syntax_Syntax.n  in
                      match uu____20221 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____20286 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____20286 with
                           | (a_b::bs1,c2) ->
                               let uu____20346 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               (a_b, uu____20346, c2))
                      | uu____20434 ->
                          let uu____20435 =
                            let uu____20441 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____20441)
                             in
                          FStar_Errors.raise_error uu____20435 r
                       in
                    (match uu____20188 with
                     | (a_b,(rest_bs,f_b::[]),lift_c) ->
                         let uu____20559 =
                           let uu____20566 =
                             let uu____20567 =
                               let uu____20568 =
                                 let uu____20575 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____20575, a)  in
                               FStar_Syntax_Syntax.NT uu____20568  in
                             [uu____20567]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____20566
                             (fun b  ->
                                let uu____20592 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____20594 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____20596 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____20598 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____20592 uu____20594 uu____20596
                                  uu____20598) r
                            in
                         (match uu____20559 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____20612 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____20612
                                then
                                  let uu____20617 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____20626 =
                                             let uu____20628 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____20628
                                              in
                                           Prims.op_Hat s uu____20626) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____20617
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____20659 =
                                           let uu____20666 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____20666, t)  in
                                         FStar_Syntax_Syntax.NT uu____20659)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____20685 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____20685
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____20691 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
                                    effect_args_from_repr f_sort uu____20691
                                      r
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____20700 =
                                             FStar_TypeChecker_Rel.layered_effect_teq
                                               env i1 i2
                                               (FStar_Pervasives_Native.Some
                                                  lift_name)
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____20700)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let lift_ct =
                                  let uu____20703 =
                                    FStar_All.pipe_right lift_c
                                      (FStar_Syntax_Subst.subst_comp substs)
                                     in
                                  FStar_All.pipe_right uu____20703
                                    FStar_Syntax_Util.comp_to_comp_typ
                                   in
                                let is =
                                  let uu____20707 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____20707 r
                                   in
                                let fml =
                                  let uu____20712 =
                                    let uu____20717 =
                                      FStar_List.hd
                                        lift_ct.FStar_Syntax_Syntax.comp_univs
                                       in
                                    let uu____20718 =
                                      let uu____20719 =
                                        FStar_List.hd
                                          lift_ct.FStar_Syntax_Syntax.effect_args
                                         in
                                      FStar_Pervasives_Native.fst uu____20719
                                       in
                                    (uu____20717, uu____20718)  in
                                  match uu____20712 with
                                  | (u1,wp) ->
                                      FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                        env u1
                                        lift_ct.FStar_Syntax_Syntax.result_typ
                                        wp FStar_Range.dummyRange
                                   in
                                (let uu____20745 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects"))
                                     &&
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme)
                                    in
                                 if uu____20745
                                 then
                                   let uu____20751 =
                                     FStar_Syntax_Print.term_to_string fml
                                      in
                                   FStar_Util.print1 "Guard for lift is: %s"
                                     uu____20751
                                 else ());
                                (let c1 =
                                   let uu____20757 =
                                     let uu____20758 =
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
                                         uu____20758;
                                       FStar_Syntax_Syntax.flags = []
                                     }  in
                                   FStar_Syntax_Syntax.mk_Comp uu____20757
                                    in
                                 (let uu____20782 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects")
                                     in
                                  if uu____20782
                                  then
                                    let uu____20787 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    FStar_Util.print1 "} Lifted comp: %s\n"
                                      uu____20787
                                  else ());
                                 (let uu____20792 =
                                    let uu____20793 =
                                      FStar_TypeChecker_Env.conj_guard g
                                        guard_f
                                       in
                                    let uu____20794 =
                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                        (FStar_TypeChecker_Common.NonTrivial
                                           fml)
                                       in
                                    FStar_TypeChecker_Env.conj_guard
                                      uu____20793 uu____20794
                                     in
                                  (c1, uu____20792)))))))))
  
let lift_tf_layered_effect_term :
  'uuuuuu20808 .
    'uuuuuu20808 ->
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
              let uu____20837 =
                let uu____20842 =
                  FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____20842
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____20837 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____20885 =
                let uu____20886 =
                  let uu____20889 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____20889
                    FStar_Syntax_Subst.compress
                   in
                uu____20886.FStar_Syntax_Syntax.n  in
              match uu____20885 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____20912::bs,uu____20914)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____20954 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____20954
                    FStar_Pervasives_Native.fst
              | uu____21060 ->
                  let uu____21061 =
                    let uu____21067 =
                      let uu____21069 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____21069
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____21067)  in
                  FStar_Errors.raise_error uu____21061
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____21096 = FStar_Syntax_Syntax.as_arg a  in
              let uu____21105 =
                let uu____21116 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____21152  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____21159 =
                  let uu____21170 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____21170]  in
                FStar_List.append uu____21116 uu____21159  in
              uu____21096 :: uu____21105  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              e.FStar_Syntax_Syntax.pos
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index  ->
        let uu____21241 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____21241 with
        | (uu____21246,t) ->
            let err n =
              let uu____21256 =
                let uu____21262 =
                  let uu____21264 = FStar_Ident.string_of_lid datacon  in
                  let uu____21266 = FStar_Util.string_of_int n  in
                  let uu____21268 = FStar_Util.string_of_int index  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____21264 uu____21266 uu____21268
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____21262)
                 in
              let uu____21272 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____21256 uu____21272  in
            let uu____21273 =
              let uu____21274 = FStar_Syntax_Subst.compress t  in
              uu____21274.FStar_Syntax_Syntax.n  in
            (match uu____21273 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____21278) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____21333  ->
                           match uu____21333 with
                           | (uu____21341,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____21350 -> true)))
                    in
                 if (FStar_List.length bs1) <= index
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index  in
                    FStar_Syntax_Util.mk_field_projector_name datacon
                      (FStar_Pervasives_Native.fst b) index)
             | uu____21384 -> err Prims.int_zero)
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub  ->
      let uu____21397 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub.FStar_Syntax_Syntax.target)
         in
      if uu____21397
      then
        let uu____21400 =
          let uu____21413 =
            FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub.FStar_Syntax_Syntax.target uu____21413
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____21400;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____21448 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____21448 with
           | (uu____21457,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____21476 =
                 let uu____21477 =
                   let uu___2535_21478 = ct  in
                   let uu____21479 =
                     let uu____21490 =
                       let uu____21499 =
                         let uu____21500 =
                           let uu____21501 =
                             let uu____21518 =
                               let uu____21529 =
                                 FStar_Syntax_Syntax.as_arg
                                   ct.FStar_Syntax_Syntax.result_typ
                                  in
                               [uu____21529; wp]  in
                             (lift_t, uu____21518)  in
                           FStar_Syntax_Syntax.Tm_app uu____21501  in
                         FStar_Syntax_Syntax.mk uu____21500
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____21499
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____21490]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2535_21478.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2535_21478.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____21479;
                     FStar_Syntax_Syntax.flags =
                       (uu___2535_21478.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____21477  in
               (uu____21476, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____21629 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____21629 with
           | (uu____21636,lift_t) ->
               let uu____21638 =
                 let uu____21639 =
                   let uu____21656 =
                     let uu____21667 = FStar_Syntax_Syntax.as_arg r  in
                     let uu____21676 =
                       let uu____21687 =
                         FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                          in
                       let uu____21696 =
                         let uu____21707 = FStar_Syntax_Syntax.as_arg e  in
                         [uu____21707]  in
                       uu____21687 :: uu____21696  in
                     uu____21667 :: uu____21676  in
                   (lift_t, uu____21656)  in
                 FStar_Syntax_Syntax.Tm_app uu____21639  in
               FStar_Syntax_Syntax.mk uu____21638 e.FStar_Syntax_Syntax.pos
            in
         let uu____21760 =
           let uu____21773 =
             FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____21773 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____21760;
           FStar_TypeChecker_Env.mlift_term =
             (match sub.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____21809  ->
                        fun uu____21810  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun sub  ->
      let uu____21833 = get_mlift_for_subeff env sub  in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub.FStar_Syntax_Syntax.source sub.FStar_Syntax_Syntax.target
        uu____21833
  
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
  