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
    let mk f = FStar_Syntax_Syntax.mk f pat.FStar_Syntax_Syntax.p  in
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
let (effect_args_from_repr :
  FStar_Syntax_Syntax.term ->
    Prims.bool -> FStar_Range.range -> FStar_Syntax_Syntax.term Prims.list)
  =
  fun repr  ->
    fun is_layered  ->
      fun r  ->
        let err uu____1184 =
          let uu____1185 =
            let uu____1191 =
              let uu____1193 = FStar_Syntax_Print.term_to_string repr  in
              let uu____1195 = FStar_Util.string_of_bool is_layered  in
              FStar_Util.format2
                "Could not get effect args from repr %s with is_layered %s"
                uu____1193 uu____1195
               in
            (FStar_Errors.Fatal_UnexpectedEffect, uu____1191)  in
          FStar_Errors.raise_error uu____1185 r  in
        let repr1 = FStar_Syntax_Subst.compress repr  in
        if is_layered
        then
          match repr1.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_app (uu____1207,uu____1208::is) ->
              FStar_All.pipe_right is
                (FStar_List.map FStar_Pervasives_Native.fst)
          | uu____1276 -> err ()
        else
          (match repr1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (uu____1281,c) ->
               let uu____1303 =
                 FStar_All.pipe_right c FStar_Syntax_Util.comp_to_comp_typ
                  in
               FStar_All.pipe_right uu____1303
                 (fun ct  ->
                    FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                      (FStar_List.map FStar_Pervasives_Native.fst))
           | uu____1338 -> err ())
  
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
                let uu____1372 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_a] env ed
                    ret_wp
                   in
                let uu____1373 =
                  let uu____1374 = FStar_Syntax_Syntax.as_arg a  in
                  let uu____1383 =
                    let uu____1394 = FStar_Syntax_Syntax.as_arg e  in
                    [uu____1394]  in
                  uu____1374 :: uu____1383  in
                FStar_Syntax_Syntax.mk_Tm_app uu____1372 uu____1373 r  in
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
              (let uu____1467 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "LayeredEffects")
                  in
               if uu____1467
               then
                 let uu____1472 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname  in
                 let uu____1474 = FStar_Syntax_Print.univ_to_string u_a  in
                 let uu____1476 = FStar_Syntax_Print.term_to_string a  in
                 let uu____1478 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print4
                   "Computing %s.return for u_a:%s, a:%s, and e:%s{\n"
                   uu____1472 uu____1474 uu____1476 uu____1478
               else ());
              (let uu____1483 =
                 let uu____1488 =
                   FStar_All.pipe_right ed
                     FStar_Syntax_Util.get_return_vc_combinator
                    in
                 FStar_TypeChecker_Env.inst_tscheme_with uu____1488 [u_a]  in
               match uu____1483 with
               | (uu____1493,return_t) ->
                   let return_t_shape_error s =
                     let uu____1508 =
                       let uu____1510 =
                         FStar_Ident.string_of_lid
                           ed.FStar_Syntax_Syntax.mname
                          in
                       let uu____1512 =
                         FStar_Syntax_Print.term_to_string return_t  in
                       FStar_Util.format3
                         "%s.return %s does not have proper shape (reason:%s)"
                         uu____1510 uu____1512 s
                        in
                     (FStar_Errors.Fatal_UnexpectedEffect, uu____1508)  in
                   let uu____1516 =
                     let uu____1545 =
                       let uu____1546 = FStar_Syntax_Subst.compress return_t
                          in
                       uu____1546.FStar_Syntax_Syntax.n  in
                     match uu____1545 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                         (FStar_List.length bs) >= (Prims.of_int (2)) ->
                         let uu____1606 = FStar_Syntax_Subst.open_comp bs c
                            in
                         (match uu____1606 with
                          | (a_b::x_b::bs1,c1) ->
                              let uu____1675 =
                                FStar_Syntax_Util.comp_to_comp_typ c1  in
                              (a_b, x_b, bs1, uu____1675))
                     | uu____1696 ->
                         let uu____1697 =
                           return_t_shape_error
                             "Either not an arrow or not enough binders"
                            in
                         FStar_Errors.raise_error uu____1697 r
                      in
                   (match uu____1516 with
                    | (a_b,x_b,rest_bs,return_ct) ->
                        let uu____1780 =
                          let uu____1787 =
                            let uu____1788 =
                              let uu____1789 =
                                let uu____1796 =
                                  FStar_All.pipe_right a_b
                                    FStar_Pervasives_Native.fst
                                   in
                                (uu____1796, a)  in
                              FStar_Syntax_Syntax.NT uu____1789  in
                            let uu____1807 =
                              let uu____1810 =
                                let uu____1811 =
                                  let uu____1818 =
                                    FStar_All.pipe_right x_b
                                      FStar_Pervasives_Native.fst
                                     in
                                  (uu____1818, e)  in
                                FStar_Syntax_Syntax.NT uu____1811  in
                              [uu____1810]  in
                            uu____1788 :: uu____1807  in
                          FStar_TypeChecker_Env.uvars_for_binders env rest_bs
                            uu____1787
                            (fun b  ->
                               let uu____1834 =
                                 FStar_Syntax_Print.binder_to_string b  in
                               let uu____1836 =
                                 let uu____1838 =
                                   FStar_Ident.string_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Util.format1 "%s.return" uu____1838
                                  in
                               let uu____1841 = FStar_Range.string_of_range r
                                  in
                               FStar_Util.format3
                                 "implicit var for binder %s of %s at %s"
                                 uu____1834 uu____1836 uu____1841) r
                           in
                        (match uu____1780 with
                         | (rest_bs_uvars,g_uvars) ->
                             let subst =
                               FStar_List.map2
                                 (fun b  ->
                                    fun t  ->
                                      let uu____1878 =
                                        let uu____1885 =
                                          FStar_All.pipe_right b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____1885, t)  in
                                      FStar_Syntax_Syntax.NT uu____1878) (a_b
                                 :: x_b :: rest_bs) (a :: e :: rest_bs_uvars)
                                in
                             let is =
                               let uu____1911 =
                                 let uu____1914 =
                                   FStar_Syntax_Subst.compress
                                     return_ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 let uu____1915 =
                                   FStar_Syntax_Util.is_layered ed  in
                                 effect_args_from_repr uu____1914 uu____1915
                                   r
                                  in
                               FStar_All.pipe_right uu____1911
                                 (FStar_List.map
                                    (FStar_Syntax_Subst.subst subst))
                                in
                             let c =
                               let uu____1922 =
                                 let uu____1923 =
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
                                     uu____1923;
                                   FStar_Syntax_Syntax.flags = []
                                 }  in
                               FStar_Syntax_Syntax.mk_Comp uu____1922  in
                             ((let uu____1947 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____1947
                               then
                                 let uu____1952 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.print1 "} c after return %s\n"
                                   uu____1952
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
              let uu____1996 =
                FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
              if uu____1996
              then mk_indexed_return env ed u_a a e r
              else
                (let uu____2006 = mk_wp_return env ed u_a a e r  in
                 (uu____2006, FStar_TypeChecker_Env.trivial_guard))
  
let (lift_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp_typ ->
      FStar_TypeChecker_Env.mlift ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c  ->
      fun lift  ->
        let uu____2031 =
          FStar_All.pipe_right
            (let uu___251_2033 = c  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___251_2033.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___251_2033.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ =
                 (uu___251_2033.FStar_Syntax_Syntax.result_typ);
               FStar_Syntax_Syntax.effect_args =
                 (uu___251_2033.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags = []
             }) FStar_Syntax_Syntax.mk_Comp
           in
        FStar_All.pipe_right uu____2031
          (lift.FStar_TypeChecker_Env.mlift_wp env)
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1_in  ->
      fun l2_in  ->
        let uu____2054 =
          let uu____2059 = FStar_TypeChecker_Env.norm_eff_name env l1_in  in
          let uu____2060 = FStar_TypeChecker_Env.norm_eff_name env l2_in  in
          (uu____2059, uu____2060)  in
        match uu____2054 with
        | (l1,l2) ->
            let uu____2063 = FStar_TypeChecker_Env.join_opt env l1 l2  in
            (match uu____2063 with
             | FStar_Pervasives_Native.Some (m,uu____2073,uu____2074) -> m
             | FStar_Pervasives_Native.None  ->
                 let uu____2087 =
                   FStar_TypeChecker_Env.exists_polymonadic_bind env l1 l2
                    in
                 (match uu____2087 with
                  | FStar_Pervasives_Native.Some (m,uu____2101) -> m
                  | FStar_Pervasives_Native.None  ->
                      let uu____2134 =
                        let uu____2140 =
                          let uu____2142 =
                            FStar_Syntax_Print.lid_to_string l1_in  in
                          let uu____2144 =
                            FStar_Syntax_Print.lid_to_string l2_in  in
                          FStar_Util.format2
                            "Effects %s and %s cannot be composed" uu____2142
                            uu____2144
                           in
                        (FStar_Errors.Fatal_EffectsCannotBeComposed,
                          uu____2140)
                         in
                      FStar_Errors.raise_error uu____2134
                        env.FStar_TypeChecker_Env.range))
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2164 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2)
           in
        if uu____2164
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
            let uu____2223 =
              FStar_TypeChecker_Env.join_opt env
                c11.FStar_Syntax_Syntax.effect_name
                c21.FStar_Syntax_Syntax.effect_name
               in
            match uu____2223 with
            | FStar_Pervasives_Native.Some (m,lift1,lift2) ->
                let uu____2251 = lift_comp env c11 lift1  in
                (match uu____2251 with
                 | (c12,g1) ->
                     let uu____2268 =
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
                          let uu____2307 = lift_comp env_x c21 lift2  in
                          match uu____2307 with
                          | (c22,g2) ->
                              let uu____2318 =
                                FStar_TypeChecker_Env.close_guard env 
                                  [x_a] g2
                                 in
                              (c22, uu____2318))
                        in
                     (match uu____2268 with
                      | (c22,g2) -> (m, c12, c22, g1, g2)))
            | FStar_Pervasives_Native.None  ->
                let rng = env.FStar_TypeChecker_Env.range  in
                let err uu____2365 =
                  let uu____2366 =
                    let uu____2372 =
                      let uu____2374 =
                        FStar_Syntax_Print.lid_to_string
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____2376 =
                        FStar_Syntax_Print.lid_to_string
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____2374
                        uu____2376
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____2372)
                     in
                  FStar_Errors.raise_error uu____2366 rng  in
                ((let uu____2391 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "LayeredEffects")
                     in
                  if uu____2391
                  then
                    let uu____2396 =
                      let uu____2398 =
                        FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp
                         in
                      FStar_All.pipe_right uu____2398
                        FStar_Syntax_Print.comp_to_string
                       in
                    let uu____2400 =
                      let uu____2402 =
                        FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                         in
                      FStar_All.pipe_right uu____2402
                        FStar_Syntax_Print.comp_to_string
                       in
                    let uu____2404 = FStar_Util.string_of_bool for_bind  in
                    FStar_Util.print3
                      "Lifting comps %s and %s with for_bind %s{\n"
                      uu____2396 uu____2400 uu____2404
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
                      let uu____2460 =
                        let uu____2465 =
                          FStar_TypeChecker_Env.push_bv env x_bv  in
                        let uu____2466 =
                          FStar_TypeChecker_Env.get_effect_decl env ret_eff
                           in
                        let uu____2467 =
                          FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
                        let uu____2468 = FStar_Syntax_Syntax.bv_to_name x_bv
                           in
                        mk_return uu____2465 uu____2466 uu____2467
                          ct.FStar_Syntax_Syntax.result_typ uu____2468 rng
                         in
                      match uu____2460 with
                      | (c_ret,g_ret) ->
                          let uu____2475 =
                            let uu____2480 =
                              FStar_Syntax_Util.comp_to_comp_typ c_ret  in
                            f_bind env ct (FStar_Pervasives_Native.Some x_bv)
                              uu____2480 [] rng
                             in
                          (match uu____2475 with
                           | (c,g_bind) ->
                               let uu____2487 =
                                 FStar_TypeChecker_Env.conj_guard g_ret
                                   g_bind
                                  in
                               (c, uu____2487))
                       in
                    let try_lift c12 c22 =
                      let p_bind_opt =
                        FStar_TypeChecker_Env.exists_polymonadic_bind env
                          c12.FStar_Syntax_Syntax.effect_name
                          c22.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____2532 =
                        FStar_All.pipe_right p_bind_opt FStar_Util.is_some
                         in
                      if uu____2532
                      then
                        let uu____2568 =
                          FStar_All.pipe_right p_bind_opt FStar_Util.must  in
                        match uu____2568 with
                        | (p,f_bind) ->
                            let uu____2635 =
                              FStar_Ident.lid_equals p
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            (if uu____2635
                             then
                               let uu____2648 = bind_with_return c12 p f_bind
                                  in
                               match uu____2648 with
                               | (c13,g) ->
                                   let uu____2665 =
                                     let uu____2674 =
                                       FStar_Syntax_Syntax.mk_Comp c22  in
                                     ((c22.FStar_Syntax_Syntax.effect_name),
                                       c13, uu____2674, g)
                                      in
                                   FStar_Pervasives_Native.Some uu____2665
                             else FStar_Pervasives_Native.None)
                      else FStar_Pervasives_Native.None  in
                    let uu____2703 =
                      let uu____2714 = try_lift c11 c21  in
                      match uu____2714 with
                      | FStar_Pervasives_Native.Some (p,c12,c22,g) ->
                          (p, c12, c22, g,
                            FStar_TypeChecker_Env.trivial_guard)
                      | FStar_Pervasives_Native.None  ->
                          let uu____2755 = try_lift c21 c11  in
                          (match uu____2755 with
                           | FStar_Pervasives_Native.Some (p,c22,c12,g) ->
                               (p, c12, c22,
                                 FStar_TypeChecker_Env.trivial_guard, g)
                           | FStar_Pervasives_Native.None  -> err ())
                       in
                    match uu____2703 with
                    | (p,c12,c22,g1,g2) ->
                        ((let uu____2812 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2812
                          then
                            let uu____2817 = FStar_Ident.string_of_lid p  in
                            let uu____2819 =
                              FStar_Syntax_Print.comp_to_string c12  in
                            let uu____2821 =
                              FStar_Syntax_Print.comp_to_string c22  in
                            FStar_Util.print3
                              "} Returning p %s, c1 %s, and c2 %s\n"
                              uu____2817 uu____2819 uu____2821
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
            let uu____2874 = lift_comps_sep_guards env c1 c2 b for_bind  in
            match uu____2874 with
            | (l,c11,c21,g1,g2) ->
                let uu____2898 = FStar_TypeChecker_Env.conj_guard g1 g2  in
                (l, c11, c21, uu____2898)
  
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
          let uu____2954 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____2954
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2966 =
      let uu____2967 = FStar_Syntax_Subst.compress t  in
      uu____2967.FStar_Syntax_Syntax.n  in
    match uu____2966 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2971 -> true
    | uu____2987 -> false
  
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
              let uu____3057 =
                let uu____3059 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____3059  in
              if uu____3057
              then f
              else (let uu____3066 = reason1 ()  in label uu____3066 r f)
  
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
            let uu___396_3087 = g  in
            let uu____3088 =
              let uu____3089 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____3089  in
            {
              FStar_TypeChecker_Common.guard_f = uu____3088;
              FStar_TypeChecker_Common.deferred =
                (uu___396_3087.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___396_3087.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___396_3087.FStar_TypeChecker_Common.implicits)
            }
  
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____3110 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____3110
        then c
        else
          (let uu____3115 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____3115
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close =
                  let uu____3157 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator
                     in
                  FStar_All.pipe_right uu____3157 FStar_Util.must  in
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____3186 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____3186]  in
                       let us =
                         let uu____3208 =
                           let uu____3211 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____3211]  in
                         u_res :: uu____3208  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____3217 =
                         FStar_TypeChecker_Env.inst_effect_fun_with us env md
                           close
                          in
                       let uu____3218 =
                         let uu____3219 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____3228 =
                           let uu____3239 =
                             FStar_Syntax_Syntax.as_arg
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____3248 =
                             let uu____3259 = FStar_Syntax_Syntax.as_arg wp1
                                in
                             [uu____3259]  in
                           uu____3239 :: uu____3248  in
                         uu____3219 :: uu____3228  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____3217 uu____3218
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____3301 = destruct_wp_comp c1  in
              match uu____3301 with
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
                let uu____3341 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____3341
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
                  let uu____3391 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs)
                     in
                  FStar_All.pipe_right uu____3391
                    (close_guard_implicits env false bs)))
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_3404  ->
            match uu___0_3404 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____3407 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____3432 =
            let uu____3435 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____3435 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____3432
            (fun c  ->
               (let uu____3459 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____3459) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____3463 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____3463)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____3474 = FStar_Syntax_Util.head_and_args' e  in
                match uu____3474 with
                | (head,uu____3491) ->
                    let uu____3512 =
                      let uu____3513 = FStar_Syntax_Util.un_uinst head  in
                      uu____3513.FStar_Syntax_Syntax.n  in
                    (match uu____3512 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____3518 =
                           let uu____3520 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____3520
                            in
                         Prims.op_Negation uu____3518
                     | uu____3521 -> true)))
              &&
              (let uu____3524 = should_not_inline_lc lc  in
               Prims.op_Negation uu____3524)
  
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
            let uu____3552 =
              let uu____3554 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____3554  in
            if uu____3552
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____3561 = FStar_Syntax_Util.is_unit t  in
               if uu____3561
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
                    let uu____3570 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____3570
                    then FStar_Syntax_Syntax.tun
                    else
                      (let ret_wp =
                         FStar_All.pipe_right m
                           FStar_Syntax_Util.get_return_vc_combinator
                          in
                       let uu____3576 =
                         let uu____3577 =
                           FStar_TypeChecker_Env.inst_effect_fun_with 
                             [u_t] env m ret_wp
                            in
                         let uu____3578 =
                           let uu____3579 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____3588 =
                             let uu____3599 = FStar_Syntax_Syntax.as_arg v
                                in
                             [uu____3599]  in
                           uu____3579 :: uu____3588  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3577 uu____3578
                           v.FStar_Syntax_Syntax.pos
                          in
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Env.Beta;
                         FStar_TypeChecker_Env.NoFullNorm] env uu____3576)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____3633 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____3633
           then
             let uu____3638 =
               FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos  in
             let uu____3640 = FStar_Syntax_Print.term_to_string v  in
             let uu____3642 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____3638 uu____3640 uu____3642
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
                      (let uu____3715 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LayeredEffects")
                          in
                       if uu____3715
                       then
                         let uu____3720 =
                           let uu____3722 = FStar_Syntax_Syntax.mk_Comp ct1
                              in
                           FStar_Syntax_Print.comp_to_string uu____3722  in
                         let uu____3723 =
                           let uu____3725 = FStar_Syntax_Syntax.mk_Comp ct2
                              in
                           FStar_Syntax_Print.comp_to_string uu____3725  in
                         FStar_Util.print2 "Binding c1:%s and c2:%s {\n"
                           uu____3720 uu____3723
                       else ());
                      (let uu____3729 =
                         let uu____3736 =
                           FStar_TypeChecker_Env.get_effect_decl env m  in
                         let uu____3737 =
                           FStar_TypeChecker_Env.get_effect_decl env n  in
                         let uu____3738 =
                           FStar_TypeChecker_Env.get_effect_decl env p  in
                         (uu____3736, uu____3737, uu____3738)  in
                       match uu____3729 with
                       | (m_ed,n_ed,p_ed) ->
                           let uu____3746 =
                             let uu____3757 =
                               FStar_List.hd
                                 ct1.FStar_Syntax_Syntax.comp_univs
                                in
                             let uu____3758 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 ct1.FStar_Syntax_Syntax.effect_args
                                in
                             (uu____3757,
                               (ct1.FStar_Syntax_Syntax.result_typ),
                               uu____3758)
                              in
                           (match uu____3746 with
                            | (u1,t1,is1) ->
                                let uu____3792 =
                                  let uu____3803 =
                                    FStar_List.hd
                                      ct2.FStar_Syntax_Syntax.comp_univs
                                     in
                                  let uu____3804 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst
                                      ct2.FStar_Syntax_Syntax.effect_args
                                     in
                                  (uu____3803,
                                    (ct2.FStar_Syntax_Syntax.result_typ),
                                    uu____3804)
                                   in
                                (match uu____3792 with
                                 | (u2,t2,is2) ->
                                     let uu____3838 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         bind_t [u1; u2]
                                        in
                                     (match uu____3838 with
                                      | (uu____3847,bind_t1) ->
                                          let bind_t_shape_error s =
                                            let uu____3862 =
                                              let uu____3864 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t1
                                                 in
                                              FStar_Util.format2
                                                "bind %s does not have proper shape (reason:%s)"
                                                uu____3864 s
                                               in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu____3862)
                                             in
                                          let uu____3868 =
                                            let uu____3913 =
                                              let uu____3914 =
                                                FStar_Syntax_Subst.compress
                                                  bind_t1
                                                 in
                                              uu____3914.FStar_Syntax_Syntax.n
                                               in
                                            match uu____3913 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs,c) when
                                                (FStar_List.length bs) >=
                                                  (Prims.of_int (4))
                                                ->
                                                let uu____3990 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs c
                                                   in
                                                (match uu____3990 with
                                                 | (a_b::b_b::bs1,c1) ->
                                                     let uu____4075 =
                                                       let uu____4102 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2)))
                                                           bs1
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____4102
                                                         (fun uu____4187  ->
                                                            match uu____4187
                                                            with
                                                            | (l1,l2) ->
                                                                let uu____4268
                                                                  =
                                                                  FStar_List.hd
                                                                    l2
                                                                   in
                                                                let uu____4281
                                                                  =
                                                                  let uu____4288
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                  FStar_List.hd
                                                                    uu____4288
                                                                   in
                                                                (l1,
                                                                  uu____4268,
                                                                  uu____4281))
                                                        in
                                                     (match uu____4075 with
                                                      | (rest_bs,f_b,g_b) ->
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b, c1)))
                                            | uu____4448 ->
                                                let uu____4449 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders"
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____4449 r1
                                             in
                                          (match uu____3868 with
                                           | (a_b,b_b,rest_bs,f_b,g_b,bind_c)
                                               ->
                                               let uu____4574 =
                                                 let uu____4581 =
                                                   let uu____4582 =
                                                     let uu____4583 =
                                                       let uu____4590 =
                                                         FStar_All.pipe_right
                                                           a_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       (uu____4590, t1)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____4583
                                                      in
                                                   let uu____4601 =
                                                     let uu____4604 =
                                                       let uu____4605 =
                                                         let uu____4612 =
                                                           FStar_All.pipe_right
                                                             b_b
                                                             FStar_Pervasives_Native.fst
                                                            in
                                                         (uu____4612, t2)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____4605
                                                        in
                                                     [uu____4604]  in
                                                   uu____4582 :: uu____4601
                                                    in
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs uu____4581
                                                   (fun b1  ->
                                                      let uu____4628 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1
                                                         in
                                                      let uu____4630 =
                                                        let uu____4632 =
                                                          FStar_Ident.string_of_lid
                                                            m
                                                           in
                                                        let uu____4634 =
                                                          FStar_Ident.string_of_lid
                                                            n
                                                           in
                                                        let uu____4636 =
                                                          FStar_Ident.string_of_lid
                                                            p
                                                           in
                                                        FStar_Util.format3
                                                          "(%s, %s) |> %s"
                                                          uu____4632
                                                          uu____4634
                                                          uu____4636
                                                         in
                                                      let uu____4639 =
                                                        FStar_Range.string_of_range
                                                          r1
                                                         in
                                                      FStar_Util.format3
                                                        "implicit var for binder %s of %s at %s"
                                                        uu____4628 uu____4630
                                                        uu____4639) r1
                                                  in
                                               (match uu____4574 with
                                                | (rest_bs_uvars,g_uvars) ->
                                                    let subst =
                                                      FStar_List.map2
                                                        (fun b1  ->
                                                           fun t  ->
                                                             let uu____4676 =
                                                               let uu____4683
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   b1
                                                                   FStar_Pervasives_Native.fst
                                                                  in
                                                               (uu____4683,
                                                                 t)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____4676)
                                                        (a_b :: b_b ::
                                                        rest_bs) (t1 :: t2 ::
                                                        rest_bs_uvars)
                                                       in
                                                    let f_guard =
                                                      let f_sort_is =
                                                        let uu____4710 =
                                                          let uu____4713 =
                                                            let uu____4714 =
                                                              let uu____4715
                                                                =
                                                                FStar_All.pipe_right
                                                                  f_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4715.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4714
                                                             in
                                                          let uu____4724 =
                                                            FStar_Syntax_Util.is_layered
                                                              m_ed
                                                             in
                                                          effect_args_from_repr
                                                            uu____4713
                                                            uu____4724 r1
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____4710
                                                          (FStar_List.map
                                                             (FStar_Syntax_Subst.subst
                                                                subst))
                                                         in
                                                      FStar_List.fold_left2
                                                        (fun g  ->
                                                           fun i1  ->
                                                             fun f_i1  ->
                                                               let uu____4737
                                                                 =
                                                                 FStar_TypeChecker_Rel.teq
                                                                   env i1
                                                                   f_i1
                                                                  in
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g uu____4737)
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
                                                        let uu____4756 =
                                                          let uu____4757 =
                                                            let uu____4760 =
                                                              let uu____4761
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4761.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4760
                                                             in
                                                          uu____4757.FStar_Syntax_Syntax.n
                                                           in
                                                        match uu____4756 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____4794 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c
                                                               in
                                                            (match uu____4794
                                                             with
                                                             | (bs1,c1) ->
                                                                 let bs_subst
                                                                   =
                                                                   let uu____4804
                                                                    =
                                                                    let uu____4811
                                                                    =
                                                                    let uu____4812
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____4812
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____4833
                                                                    =
                                                                    let uu____4836
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4836
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____4811,
                                                                    uu____4833)
                                                                     in
                                                                   FStar_Syntax_Syntax.NT
                                                                    uu____4804
                                                                    in
                                                                 let c2 =
                                                                   FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1
                                                                    in
                                                                 let uu____4850
                                                                   =
                                                                   let uu____4853
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2)  in
                                                                   let uu____4854
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed  in
                                                                   effect_args_from_repr
                                                                    uu____4853
                                                                    uu____4854
                                                                    r1
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____4850
                                                                   (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst)))
                                                        | uu____4860 ->
                                                            failwith
                                                              "impossible: mk_indexed_bind"
                                                         in
                                                      let env_g =
                                                        FStar_TypeChecker_Env.push_binders
                                                          env [x_a]
                                                         in
                                                      let uu____4877 =
                                                        FStar_List.fold_left2
                                                          (fun g  ->
                                                             fun i1  ->
                                                               fun g_i1  ->
                                                                 let uu____4885
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq
                                                                    env_g i1
                                                                    g_i1
                                                                    in
                                                                 FStar_TypeChecker_Env.conj_guard
                                                                   g
                                                                   uu____4885)
                                                          FStar_TypeChecker_Env.trivial_guard
                                                          is2 g_sort_is
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4877
                                                        (FStar_TypeChecker_Env.close_guard
                                                           env [x_a])
                                                       in
                                                    let bind_ct =
                                                      let uu____4899 =
                                                        FStar_All.pipe_right
                                                          bind_c
                                                          (FStar_Syntax_Subst.subst_comp
                                                             subst)
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4899
                                                        FStar_Syntax_Util.comp_to_comp_typ
                                                       in
                                                    let fml =
                                                      let uu____4901 =
                                                        let uu____4906 =
                                                          FStar_List.hd
                                                            bind_ct.FStar_Syntax_Syntax.comp_univs
                                                           in
                                                        let uu____4907 =
                                                          let uu____4908 =
                                                            FStar_List.hd
                                                              bind_ct.FStar_Syntax_Syntax.effect_args
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____4908
                                                           in
                                                        (uu____4906,
                                                          uu____4907)
                                                         in
                                                      match uu____4901 with
                                                      | (u,wp) ->
                                                          FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                            env u
                                                            bind_ct.FStar_Syntax_Syntax.result_typ
                                                            wp
                                                            FStar_Range.dummyRange
                                                       in
                                                    let is =
                                                      let uu____4934 =
                                                        FStar_Syntax_Subst.compress
                                                          bind_ct.FStar_Syntax_Syntax.result_typ
                                                         in
                                                      let uu____4935 =
                                                        FStar_Syntax_Util.is_layered
                                                          p_ed
                                                         in
                                                      effect_args_from_repr
                                                        uu____4934 uu____4935
                                                        r1
                                                       in
                                                    let c =
                                                      let uu____4938 =
                                                        let uu____4939 =
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
                                                            = uu____4939;
                                                          FStar_Syntax_Syntax.flags
                                                            = flags
                                                        }  in
                                                      FStar_Syntax_Syntax.mk_Comp
                                                        uu____4938
                                                       in
                                                    ((let uu____4959 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "LayeredEffects")
                                                         in
                                                      if uu____4959
                                                      then
                                                        let uu____4964 =
                                                          FStar_Syntax_Print.comp_to_string
                                                            c
                                                           in
                                                        FStar_Util.print1
                                                          "} c after bind: %s\n"
                                                          uu____4964
                                                      else ());
                                                     (let uu____4969 =
                                                        let uu____4970 =
                                                          let uu____4973 =
                                                            let uu____4976 =
                                                              let uu____4979
                                                                =
                                                                let uu____4982
                                                                  =
                                                                  FStar_TypeChecker_Env.guard_of_guard_formula
                                                                    (
                                                                    FStar_TypeChecker_Common.NonTrivial
                                                                    fml)
                                                                   in
                                                                [uu____4982]
                                                                 in
                                                              g_guard ::
                                                                uu____4979
                                                               in
                                                            f_guard ::
                                                              uu____4976
                                                             in
                                                          g_uvars ::
                                                            uu____4973
                                                           in
                                                        FStar_TypeChecker_Env.conj_guards
                                                          uu____4970
                                                         in
                                                      (c, uu____4969)))))))))
  
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
                let uu____5027 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____5053 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____5053 with
                  | (a,kwp) ->
                      let uu____5084 = destruct_wp_comp ct1  in
                      let uu____5091 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____5084, uu____5091)
                   in
                match uu____5027 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____5144 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____5144]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____5164 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____5164]
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
                      let uu____5211 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____5220 =
                        let uu____5231 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____5240 =
                          let uu____5251 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____5260 =
                            let uu____5271 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____5280 =
                              let uu____5291 =
                                let uu____5300 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____5300  in
                              [uu____5291]  in
                            uu____5271 :: uu____5280  in
                          uu____5251 :: uu____5260  in
                        uu____5231 :: uu____5240  in
                      uu____5211 :: uu____5220  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____5351 =
                        FStar_TypeChecker_Env.inst_effect_fun_with
                          [u_t1; u_t2] env md bind_wp
                         in
                      FStar_Syntax_Syntax.mk_Tm_app uu____5351 wp_args
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
              let uu____5399 =
                let uu____5404 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
                let uu____5405 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
                (uu____5404, uu____5405)  in
              match uu____5399 with
              | (ct1,ct2) ->
                  let uu____5412 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name
                     in
                  (match uu____5412 with
                   | FStar_Pervasives_Native.Some (p,f_bind) ->
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None  ->
                       let uu____5463 = lift_comps env c1 c2 b true  in
                       (match uu____5463 with
                        | (m,c11,c21,g_lift) ->
                            let uu____5481 =
                              let uu____5486 =
                                FStar_Syntax_Util.comp_to_comp_typ c11  in
                              let uu____5487 =
                                FStar_Syntax_Util.comp_to_comp_typ c21  in
                              (uu____5486, uu____5487)  in
                            (match uu____5481 with
                             | (ct11,ct21) ->
                                 let uu____5494 =
                                   let uu____5499 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m
                                      in
                                   if uu____5499
                                   then
                                     let bind_t =
                                       let uu____5507 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env)
                                          in
                                       FStar_All.pipe_right uu____5507
                                         FStar_Syntax_Util.get_bind_vc_combinator
                                        in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu____5510 =
                                        mk_wp_bind env m ct11 b ct21 flags r1
                                         in
                                      (uu____5510,
                                        FStar_TypeChecker_Env.trivial_guard))
                                    in
                                 (match uu____5494 with
                                  | (c,g_bind) ->
                                      let uu____5517 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind
                                         in
                                      (c, uu____5517)))))
  
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
            let uu____5553 =
              let uu____5554 =
                let uu____5565 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____5565]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____5554;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____5553  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____5610 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_5616  ->
              match uu___1_5616 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5619 -> false))
       in
    if uu____5610
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_5631  ->
              match uu___2_5631 with
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
        let uu____5659 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5659
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____5670 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____5670  in
           let pure_assume_wp1 =
             let uu____5673 =
               let uu____5674 =
                 FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
               [uu____5674]  in
             let uu____5707 = FStar_TypeChecker_Env.get_range env  in
             FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____5673
               uu____5707
              in
           let uu____5708 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____5708)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5736 =
          let uu____5737 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5737 with
          | (c,g_c) ->
              let uu____5748 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5748
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5762 = weaken_comp env c f1  in
                     (match uu____5762 with
                      | (c1,g_w) ->
                          let uu____5773 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____5773)))
           in
        let uu____5774 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5774 weaken
  
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
                 let uu____5831 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____5831  in
               let pure_assert_wp1 =
                 let uu____5834 =
                   let uu____5835 =
                     let uu____5844 = label_opt env reason r f  in
                     FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                       uu____5844
                      in
                   [uu____5835]  in
                 FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____5834 r
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
            let uu____5914 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____5914
            then (lc, g0)
            else
              (let flags =
                 let uu____5926 =
                   let uu____5934 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____5934
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5926 with
                 | (maybe_trivial_post,flags) ->
                     let uu____5964 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_5972  ->
                               match uu___3_5972 with
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
                               | uu____5975 -> []))
                        in
                     FStar_List.append flags uu____5964
                  in
               let strengthen uu____5985 =
                 let uu____5986 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____5986 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____6005 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____6005 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____6012 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____6012
                              then
                                let uu____6016 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____6018 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____6016 uu____6018
                              else ());
                             (let uu____6023 =
                                strengthen_comp env reason c f flags  in
                              match uu____6023 with
                              | (c1,g_s) ->
                                  let uu____6034 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____6034))))
                  in
               let uu____6035 =
                 let uu____6036 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____6036
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____6035,
                 (let uu___707_6038 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___707_6038.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___707_6038.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___707_6038.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_6047  ->
            match uu___4_6047 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____6051 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____6080 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____6080
          then e
          else
            (let uu____6087 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____6090 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____6090)
                in
             if uu____6087
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
                | uu____6160 -> false  in
              if is_unit
              then
                let uu____6167 =
                  let uu____6169 =
                    let uu____6170 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____6170
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____6169
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____6167
                 then
                   let uu____6179 = FStar_Syntax_Subst.open_term_bv b phi  in
                   match uu____6179 with
                   | (b1,phi1) ->
                       let phi2 =
                         FStar_Syntax_Subst.subst
                           [FStar_Syntax_Syntax.NT
                              (b1, FStar_Syntax_Syntax.unit_const)] phi1
                          in
                       weaken_comp env c phi2
                 else
                   (let uu____6195 = close_wp_comp env [x] c  in
                    (uu____6195, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____6198 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
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
          fun uu____6226  ->
            match uu____6226 with
            | (b,lc2) ->
                let debug f =
                  let uu____6246 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____6246 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____6259 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____6259
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____6269 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____6269
                       then
                         let uu____6274 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____6274
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____6281 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____6281
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____6290 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____6290
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____6297 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____6297
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____6313 =
                  let uu____6314 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____6314
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____6322 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____6322, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____6325 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____6325 with
                     | (c1,g_c1) ->
                         let uu____6336 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____6336 with
                          | (c2,g_c2) ->
                              let trivial_guard =
                                let uu____6348 =
                                  match b with
                                  | FStar_Pervasives_Native.Some x ->
                                      let b1 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      let uu____6351 =
                                        FStar_Syntax_Syntax.is_null_binder b1
                                         in
                                      if uu____6351
                                      then g_c2
                                      else
                                        FStar_TypeChecker_Env.close_guard env
                                          [b1] g_c2
                                  | FStar_Pervasives_Native.None  -> g_c2  in
                                FStar_TypeChecker_Env.conj_guard g_c1
                                  uu____6348
                                 in
                              (debug
                                 (fun uu____6377  ->
                                    let uu____6378 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____6380 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____6385 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____6378 uu____6380 uu____6385);
                               (let aux uu____6403 =
                                  let uu____6404 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____6404
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____6435
                                        ->
                                        let uu____6436 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____6436
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____6468 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____6468
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____6515 =
                                  let aux_with_trivial_guard uu____6545 =
                                    let uu____6546 = aux ()  in
                                    match uu____6546 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c, trivial_guard, reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____6604 =
                                    let uu____6606 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____6606  in
                                  if uu____6604
                                  then
                                    let uu____6622 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____6622
                                     then
                                       FStar_Util.Inl
                                         (c2, trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____6649 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____6649))
                                  else
                                    (let uu____6666 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____6666
                                     then
                                       let close_with_type_of_x x c =
                                         let x1 =
                                           let uu___810_6697 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___810_6697.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___810_6697.FStar_Syntax_Syntax.index);
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
                                           let uu____6728 =
                                             let uu____6733 =
                                               FStar_All.pipe_right c2
                                                 (FStar_Syntax_Subst.subst_comp
                                                    [FStar_Syntax_Syntax.NT
                                                       (x, e)])
                                                in
                                             FStar_All.pipe_right uu____6733
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6728 with
                                            | (c21,g_close) ->
                                                let uu____6754 =
                                                  let uu____6762 =
                                                    let uu____6763 =
                                                      let uu____6766 =
                                                        let uu____6769 =
                                                          FStar_TypeChecker_Env.map_guard
                                                            g_c2
                                                            (FStar_Syntax_Subst.subst
                                                               [FStar_Syntax_Syntax.NT
                                                                  (x, e)])
                                                           in
                                                        [uu____6769; g_close]
                                                         in
                                                      g_c1 :: uu____6766  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6763
                                                     in
                                                  (c21, uu____6762, "c1 Tot")
                                                   in
                                                FStar_Util.Inl uu____6754)
                                       | (uu____6782,FStar_Pervasives_Native.Some
                                          x) ->
                                           let uu____6794 =
                                             FStar_All.pipe_right c2
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6794 with
                                            | (c21,g_close) ->
                                                let uu____6817 =
                                                  let uu____6825 =
                                                    let uu____6826 =
                                                      let uu____6829 =
                                                        let uu____6832 =
                                                          let uu____6833 =
                                                            let uu____6834 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____6834]  in
                                                          FStar_TypeChecker_Env.close_guard
                                                            env uu____6833
                                                            g_c2
                                                           in
                                                        [uu____6832; g_close]
                                                         in
                                                      g_c1 :: uu____6829  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6826
                                                     in
                                                  (c21, uu____6825,
                                                    "c1 Tot only close")
                                                   in
                                                FStar_Util.Inl uu____6817)
                                       | (uu____6863,uu____6864) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____6879 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____6879
                                        then
                                          let uu____6894 =
                                            let uu____6902 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____6902, trivial_guard,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____6894
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____6915 = try_simplify ()  in
                                match uu____6915 with
                                | FStar_Util.Inl (c,g,reason) ->
                                    (debug
                                       (fun uu____6950  ->
                                          let uu____6951 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____6951);
                                     (c, g))
                                | FStar_Util.Inr reason ->
                                    (debug
                                       (fun uu____6967  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 g =
                                        let uu____6998 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____6998 with
                                        | (c,g_bind) ->
                                            let uu____7009 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g g_bind
                                               in
                                            (c, uu____7009)
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
                                        let uu____7036 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____7036 with
                                        | (m,uu____7048,lift2) ->
                                            let uu____7050 =
                                              lift_comp env c22 lift2  in
                                            (match uu____7050 with
                                             | (c23,g2) ->
                                                 let uu____7061 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____7061 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let trivial =
                                                        let uu____7077 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7077
                                                          FStar_Util.must
                                                         in
                                                      let vc1 =
                                                        let uu____7085 =
                                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                                            [u1] env
                                                            md_pure_or_ghost
                                                            trivial
                                                           in
                                                        let uu____7086 =
                                                          let uu____7087 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              t1
                                                             in
                                                          let uu____7096 =
                                                            let uu____7107 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                wp1
                                                               in
                                                            [uu____7107]  in
                                                          uu____7087 ::
                                                            uu____7096
                                                           in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7085
                                                          uu____7086 r1
                                                         in
                                                      let uu____7140 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____7140 with
                                                       | (c,g_s) ->
                                                           let uu____7155 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____7155))))
                                         in
                                      let uu____7156 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____7172 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____7172, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____7156 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____7188 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____7188
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____7197 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____7197
                                             then
                                               (debug
                                                  (fun uu____7211  ->
                                                     let uu____7212 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____7214 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____7212 uu____7214);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 let g =
                                                   let uu____7221 =
                                                     FStar_TypeChecker_Env.map_guard
                                                       g_c2
                                                       (FStar_Syntax_Subst.subst
                                                          [FStar_Syntax_Syntax.NT
                                                             (x, e1)])
                                                      in
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 uu____7221
                                                    in
                                                 mk_bind1 c1 b c21 g))
                                             else
                                               (let uu____7226 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____7229 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____7229)
                                                   in
                                                if uu____7226
                                                then
                                                  let e1' =
                                                    let uu____7254 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____7254
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug
                                                     (fun uu____7266  ->
                                                        let uu____7267 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____7269 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____7267
                                                          uu____7269);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug
                                                     (fun uu____7284  ->
                                                        let uu____7285 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____7287 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____7285
                                                          uu____7287);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____7294 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____7294
                                                       in
                                                    let uu____7295 =
                                                      let uu____7300 =
                                                        let uu____7301 =
                                                          let uu____7302 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____7302]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____7301
                                                         in
                                                      weaken_comp uu____7300
                                                        c21 x_eq_e
                                                       in
                                                    match uu____7295 with
                                                    | (c22,g_w) ->
                                                        let g =
                                                          let uu____7328 =
                                                            let uu____7329 =
                                                              let uu____7330
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x
                                                                 in
                                                              [uu____7330]
                                                               in
                                                            let uu____7349 =
                                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                                g_c2 x_eq_e
                                                               in
                                                            FStar_TypeChecker_Env.close_guard
                                                              env uu____7329
                                                              uu____7349
                                                             in
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g_c1 uu____7328
                                                           in
                                                        let uu____7350 =
                                                          mk_bind1 c1 b c22 g
                                                           in
                                                        (match uu____7350
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____7361 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____7361))))))
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
      | uu____7378 -> g2
  
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
            (let uu____7402 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____7402)
           in
        let flags =
          if should_return1
          then
            let uu____7410 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____7410
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine uu____7428 =
          let uu____7429 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____7429 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____7442 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____7442
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____7450 =
                  let uu____7452 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____7452  in
                (if uu____7450
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___935_7461 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___935_7461.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___935_7461.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___935_7461.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____7462 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____7462, g_c)
                 else
                   (let uu____7465 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____7465, g_c)))
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
                   let uu____7476 =
                     let uu____7477 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____7477
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____7476
                    in
                 let eq = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret
                     (FStar_TypeChecker_Common.NonTrivial eq)
                    in
                 let uu____7480 =
                   let uu____7485 =
                     let uu____7486 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____7486
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____7485  in
                 match uu____7480 with
                 | (bind_c,g_bind) ->
                     let uu____7495 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____7496 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____7495, uu____7496))
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
            fun uu____7532  ->
              match uu____7532 with
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
                    let uu____7544 =
                      ((let uu____7548 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____7548) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____7544
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____7566 =
        let uu____7567 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____7567  in
      FStar_Syntax_Syntax.fvar uu____7566 FStar_Syntax_Syntax.delta_constant
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
                  let uu____7617 =
                    let uu____7622 =
                      let uu____7623 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____7623 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7622 [u_a]
                     in
                  match uu____7617 with
                  | (uu____7634,conjunction) ->
                      let uu____7636 =
                        let uu____7645 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____7660 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____7645, uu____7660)  in
                      (match uu____7636 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____7706 =
                               let uu____7708 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____7708 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7706)
                              in
                           let uu____7712 =
                             let uu____7757 =
                               let uu____7758 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____7758.FStar_Syntax_Syntax.n  in
                             match uu____7757 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____7807) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____7839 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____7839 with
                                  | (a_b::bs1,body1) ->
                                      let uu____7911 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____7911 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____8059 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____8059)))
                             | uu____8092 ->
                                 let uu____8093 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____8093 r
                              in
                           (match uu____7712 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____8218 =
                                  let uu____8225 =
                                    let uu____8226 =
                                      let uu____8227 =
                                        let uu____8234 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____8234, a)  in
                                      FStar_Syntax_Syntax.NT uu____8227  in
                                    [uu____8226]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____8225
                                    (fun b  ->
                                       let uu____8250 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____8252 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____8254 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____8250 uu____8252 uu____8254) r
                                   in
                                (match uu____8218 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____8292 =
                                                let uu____8299 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____8299, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____8292) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____8338 =
                                           let uu____8339 =
                                             let uu____8342 =
                                               let uu____8343 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8343.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8342
                                              in
                                           uu____8339.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8338 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8354,uu____8355::is) ->
                                             let uu____8397 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8397
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8430 ->
                                             let uu____8431 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8431 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____8447 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8447)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____8452 =
                                           let uu____8453 =
                                             let uu____8456 =
                                               let uu____8457 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8457.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8456
                                              in
                                           uu____8453.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8452 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8468,uu____8469::is) ->
                                             let uu____8511 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8511
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8544 ->
                                             let uu____8545 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8545 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____8561 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8561)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____8566 =
                                         let uu____8567 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____8567.FStar_Syntax_Syntax.n  in
                                       match uu____8566 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8572,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8627 ->
                                           let uu____8628 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____8628 r
                                        in
                                     let uu____8637 =
                                       let uu____8638 =
                                         let uu____8639 =
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
                                             uu____8639;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____8638
                                        in
                                     let uu____8662 =
                                       let uu____8663 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8663 g_guard
                                        in
                                     (uu____8637, uu____8662))))
  
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
                fun uu____8708  ->
                  let if_then_else =
                    let uu____8714 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____8714 FStar_Util.must  in
                  let uu____8721 = destruct_wp_comp ct1  in
                  match uu____8721 with
                  | (uu____8732,uu____8733,wp_t) ->
                      let uu____8735 = destruct_wp_comp ct2  in
                      (match uu____8735 with
                       | (uu____8746,uu____8747,wp_e) ->
                           let wp =
                             let uu____8750 =
                               FStar_TypeChecker_Env.inst_effect_fun_with
                                 [u_a] env ed if_then_else
                                in
                             let uu____8751 =
                               let uu____8752 = FStar_Syntax_Syntax.as_arg a
                                  in
                               let uu____8761 =
                                 let uu____8772 =
                                   FStar_Syntax_Syntax.as_arg p  in
                                 let uu____8781 =
                                   let uu____8792 =
                                     FStar_Syntax_Syntax.as_arg wp_t  in
                                   let uu____8801 =
                                     let uu____8812 =
                                       FStar_Syntax_Syntax.as_arg wp_e  in
                                     [uu____8812]  in
                                   uu____8792 :: uu____8801  in
                                 uu____8772 :: uu____8781  in
                               uu____8752 :: uu____8761  in
                             let uu____8861 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Syntax.mk_Tm_app uu____8750
                               uu____8751 uu____8861
                              in
                           let uu____8862 = mk_comp ed u_a a wp []  in
                           (uu____8862, FStar_TypeChecker_Env.trivial_guard))
  
let (comp_pure_wp_false :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun u  ->
      fun t  ->
        let post_k =
          let uu____8882 =
            let uu____8891 = FStar_Syntax_Syntax.null_binder t  in
            [uu____8891]  in
          let uu____8910 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
          FStar_Syntax_Util.arrow uu____8882 uu____8910  in
        let kwp =
          let uu____8916 =
            let uu____8925 = FStar_Syntax_Syntax.null_binder post_k  in
            [uu____8925]  in
          let uu____8944 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
          FStar_Syntax_Util.arrow uu____8916 uu____8944  in
        let post =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k  in
        let wp =
          let uu____8951 =
            let uu____8952 = FStar_Syntax_Syntax.mk_binder post  in
            [uu____8952]  in
          let uu____8971 = fvar_const env FStar_Parser_Const.false_lid  in
          FStar_Syntax_Util.abs uu____8951 uu____8971
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
            let uu____9030 =
              let uu____9031 =
                FStar_All.pipe_right scrutinee FStar_Syntax_Syntax.mk_binder
                 in
              [uu____9031]  in
            FStar_TypeChecker_Env.push_binders env0 uu____9030  in
          let eff =
            FStar_List.fold_left
              (fun eff  ->
                 fun uu____9078  ->
                   match uu____9078 with
                   | (uu____9092,eff_label,uu____9094,uu____9095) ->
                       join_effects env eff eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases
             in
          let uu____9108 =
            let uu____9116 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu____9154  ->
                      match uu____9154 with
                      | (uu____9169,uu____9170,flags,uu____9172) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___5_9189  ->
                                  match uu___5_9189 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                      true
                                  | uu____9192 -> false))))
               in
            if uu____9116
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, [])  in
          match uu____9108 with
          | (should_not_inline_whole_match,bind_cases_flags) ->
              let bind_cases uu____9229 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                   in
                let uu____9231 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                   in
                if uu____9231
                then
                  let uu____9238 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                     in
                  (uu____9238, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let maybe_return eff_label_then cthen =
                     let uu____9259 =
                       should_not_inline_whole_match ||
                         (let uu____9262 = is_pure_or_ghost_effect env eff
                             in
                          Prims.op_Negation uu____9262)
                        in
                     if uu____9259 then cthen true else cthen false  in
                   let uu____9269 =
                     let uu____9280 =
                       let uu____9293 =
                         let uu____9298 =
                           let uu____9309 =
                             FStar_All.pipe_right lcases
                               (FStar_List.map
                                  (fun uu____9359  ->
                                     match uu____9359 with
                                     | (g,uu____9378,uu____9379,uu____9380)
                                         -> g))
                              in
                           FStar_All.pipe_right uu____9309
                             (FStar_List.fold_left
                                (fun uu____9428  ->
                                   fun g  ->
                                     match uu____9428 with
                                     | (conds,acc) ->
                                         let cond =
                                           let uu____9469 =
                                             FStar_Syntax_Util.mk_neg g  in
                                           FStar_Syntax_Util.mk_conj acc
                                             uu____9469
                                            in
                                         ((FStar_List.append conds [cond]),
                                           cond))
                                ([FStar_Syntax_Util.t_true],
                                  FStar_Syntax_Util.t_true))
                            in
                         FStar_All.pipe_right uu____9298
                           FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____9293
                         (fun l  ->
                            FStar_List.splitAt
                              ((FStar_List.length l) - Prims.int_one) l)
                        in
                     FStar_All.pipe_right uu____9280
                       (fun uu____9567  ->
                          match uu____9567 with
                          | (l1,l2) ->
                              let uu____9608 = FStar_List.hd l2  in
                              (l1, uu____9608))
                      in
                   match uu____9269 with
                   | (neg_branch_conds,exhaustiveness_branch_cond) ->
                       let uu____9637 =
                         match lcases with
                         | [] ->
                             let uu____9668 =
                               comp_pure_wp_false env u_res_t res_t  in
                             (FStar_Pervasives_Native.None, uu____9668,
                               FStar_TypeChecker_Env.trivial_guard)
                         | uu____9671 ->
                             let uu____9688 =
                               let uu____9721 =
                                 let uu____9732 =
                                   FStar_All.pipe_right neg_branch_conds
                                     (FStar_List.splitAt
                                        ((FStar_List.length lcases) -
                                           Prims.int_one))
                                    in
                                 FStar_All.pipe_right uu____9732
                                   (fun uu____9804  ->
                                      match uu____9804 with
                                      | (l1,l2) ->
                                          let uu____9845 = FStar_List.hd l2
                                             in
                                          (l1, uu____9845))
                                  in
                               match uu____9721 with
                               | (neg_branch_conds1,neg_last) ->
                                   let uu____9902 =
                                     let uu____9941 =
                                       FStar_All.pipe_right lcases
                                         (FStar_List.splitAt
                                            ((FStar_List.length lcases) -
                                               Prims.int_one))
                                        in
                                     FStar_All.pipe_right uu____9941
                                       (fun uu____10153  ->
                                          match uu____10153 with
                                          | (l1,l2) ->
                                              let uu____10304 =
                                                FStar_List.hd l2  in
                                              (l1, uu____10304))
                                      in
                                   (match uu____9902 with
                                    | (lcases1,(g_last,eff_last,uu____10406,c_last))
                                        ->
                                        let uu____10476 =
                                          let lc =
                                            maybe_return eff_last c_last  in
                                          let uu____10482 =
                                            FStar_TypeChecker_Common.lcomp_comp
                                              lc
                                             in
                                          match uu____10482 with
                                          | (c,g) ->
                                              let uu____10493 =
                                                let uu____10494 =
                                                  FStar_Syntax_Util.mk_conj
                                                    g_last neg_last
                                                   in
                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                  g uu____10494
                                                 in
                                              (c, uu____10493)
                                           in
                                        (match uu____10476 with
                                         | (c,g) ->
                                             let uu____10529 =
                                               let uu____10530 =
                                                 FStar_All.pipe_right
                                                   eff_last
                                                   (FStar_TypeChecker_Env.norm_eff_name
                                                      env)
                                                  in
                                               FStar_All.pipe_right
                                                 uu____10530
                                                 (FStar_TypeChecker_Env.get_effect_decl
                                                    env)
                                                in
                                             (lcases1, neg_branch_conds1,
                                               uu____10529, c, g)))
                                in
                             (match uu____9688 with
                              | (lcases1,neg_branch_conds1,md,comp,g_comp) ->
                                  FStar_List.fold_right2
                                    (fun uu____10662  ->
                                       fun neg_cond  ->
                                         fun uu____10664  ->
                                           match (uu____10662, uu____10664)
                                           with
                                           | ((g,eff_label,uu____10724,cthen),
                                              (uu____10726,celse,g_comp1)) ->
                                               let uu____10773 =
                                                 let uu____10778 =
                                                   maybe_return eff_label
                                                     cthen
                                                    in
                                                 FStar_TypeChecker_Common.lcomp_comp
                                                   uu____10778
                                                  in
                                               (match uu____10773 with
                                                | (cthen1,g_then) ->
                                                    let uu____10789 =
                                                      let uu____10800 =
                                                        lift_comps_sep_guards
                                                          env cthen1 celse
                                                          FStar_Pervasives_Native.None
                                                          false
                                                         in
                                                      match uu____10800 with
                                                      | (m,cthen2,celse1,g_lift_then,g_lift_else)
                                                          ->
                                                          let md1 =
                                                            FStar_TypeChecker_Env.get_effect_decl
                                                              env m
                                                             in
                                                          let uu____10828 =
                                                            FStar_All.pipe_right
                                                              cthen2
                                                              FStar_Syntax_Util.comp_to_comp_typ
                                                             in
                                                          let uu____10829 =
                                                            FStar_All.pipe_right
                                                              celse1
                                                              FStar_Syntax_Util.comp_to_comp_typ
                                                             in
                                                          (md1, uu____10828,
                                                            uu____10829,
                                                            g_lift_then,
                                                            g_lift_else)
                                                       in
                                                    (match uu____10789 with
                                                     | (md1,ct_then,ct_else,g_lift_then,g_lift_else)
                                                         ->
                                                         let fn =
                                                           let uu____10880 =
                                                             FStar_All.pipe_right
                                                               md1
                                                               FStar_Syntax_Util.is_layered
                                                              in
                                                           if uu____10880
                                                           then
                                                             mk_layered_conjunction
                                                           else
                                                             mk_non_layered_conjunction
                                                            in
                                                         let uu____10914 =
                                                           let uu____10919 =
                                                             FStar_TypeChecker_Env.get_range
                                                               env
                                                              in
                                                           fn env md1 u_res_t
                                                             res_t g ct_then
                                                             ct_else
                                                             uu____10919
                                                            in
                                                         (match uu____10914
                                                          with
                                                          | (c,g_conjunction)
                                                              ->
                                                              let g_then1 =
                                                                let uu____10931
                                                                  =
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_then
                                                                    g_lift_then
                                                                   in
                                                                let uu____10932
                                                                  =
                                                                  FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    g
                                                                   in
                                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                                  uu____10931
                                                                  uu____10932
                                                                 in
                                                              let g_else =
                                                                let uu____10934
                                                                  =
                                                                  let uu____10935
                                                                    =
                                                                    FStar_Syntax_Util.mk_neg
                                                                    g  in
                                                                  FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    uu____10935
                                                                   in
                                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                                  g_lift_else
                                                                  uu____10934
                                                                 in
                                                              let uu____10938
                                                                =
                                                                FStar_TypeChecker_Env.conj_guards
                                                                  [g_comp1;
                                                                  g_then1;
                                                                  g_else;
                                                                  g_conjunction]
                                                                 in
                                                              ((FStar_Pervasives_Native.Some
                                                                  md1), c,
                                                                uu____10938)))))
                                    lcases1 neg_branch_conds1
                                    ((FStar_Pervasives_Native.Some md), comp,
                                      g_comp))
                          in
                       (match uu____9637 with
                        | (md,comp,g_comp) ->
                            let uu____10954 =
                              let uu____10959 =
                                let check =
                                  FStar_Syntax_Util.mk_imp
                                    exhaustiveness_branch_cond
                                    FStar_Syntax_Util.t_false
                                   in
                                let check1 =
                                  let uu____10966 =
                                    FStar_TypeChecker_Env.get_range env  in
                                  label
                                    FStar_TypeChecker_Err.exhaustiveness_check
                                    uu____10966 check
                                   in
                                strengthen_comp env
                                  FStar_Pervasives_Native.None comp check1
                                  bind_cases_flags
                                 in
                              match uu____10959 with
                              | (c,g) ->
                                  let uu____10977 =
                                    FStar_TypeChecker_Env.conj_guard g_comp g
                                     in
                                  (c, uu____10977)
                               in
                            (match uu____10954 with
                             | (comp1,g_comp1) ->
                                 let g_comp2 =
                                   let uu____10985 =
                                     let uu____10986 =
                                       FStar_All.pipe_right scrutinee
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     [uu____10986]  in
                                   FStar_TypeChecker_Env.close_guard env0
                                     uu____10985 g_comp1
                                    in
                                 (match lcases with
                                  | [] -> (comp1, g_comp2)
                                  | uu____11029::[] -> (comp1, g_comp2)
                                  | uu____11072 ->
                                      let uu____11089 =
                                        let uu____11091 =
                                          FStar_All.pipe_right md
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____11091
                                          FStar_Syntax_Util.is_layered
                                         in
                                      if uu____11089
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
                                         let uu____11104 =
                                           destruct_wp_comp comp2  in
                                         match uu____11104 with
                                         | (uu____11115,uu____11116,wp) ->
                                             let ite_wp =
                                               let uu____11119 =
                                                 FStar_All.pipe_right md1
                                                   FStar_Syntax_Util.get_wp_ite_combinator
                                                  in
                                               FStar_All.pipe_right
                                                 uu____11119 FStar_Util.must
                                                in
                                             let wp1 =
                                               let uu____11127 =
                                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                                   [u_res_t] env md1 ite_wp
                                                  in
                                               let uu____11128 =
                                                 let uu____11129 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     res_t
                                                    in
                                                 let uu____11138 =
                                                   let uu____11149 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp
                                                      in
                                                   [uu____11149]  in
                                                 uu____11129 :: uu____11138
                                                  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu____11127 uu____11128
                                                 wp.FStar_Syntax_Syntax.pos
                                                in
                                             let uu____11182 =
                                               mk_comp md1 u_res_t res_t wp1
                                                 bind_cases_flags
                                                in
                                             (uu____11182, g_comp2))))))
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
          let uu____11217 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____11217 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____11233 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____11239 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____11233 uu____11239
              else
                (let uu____11248 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____11254 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____11248 uu____11254)
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
          let uu____11279 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____11279
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____11282 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____11282
        then u_res
        else
          (let is_total =
             let uu____11289 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____11289
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____11300 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____11300 with
              | FStar_Pervasives_Native.None  ->
                  let uu____11303 =
                    let uu____11309 =
                      let uu____11311 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____11311
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____11309)
                     in
                  FStar_Errors.raise_error uu____11303
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
      let uu____11335 = destruct_wp_comp ct  in
      match uu____11335 with
      | (u_t,t,wp) ->
          let vc =
            let uu____11352 =
              let uu____11353 =
                let uu____11354 =
                  FStar_All.pipe_right md
                    FStar_Syntax_Util.get_wp_trivial_combinator
                   in
                FStar_All.pipe_right uu____11354 FStar_Util.must  in
              FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                uu____11353
               in
            let uu____11361 =
              let uu____11362 = FStar_Syntax_Syntax.as_arg t  in
              let uu____11371 =
                let uu____11382 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____11382]  in
              uu____11362 :: uu____11371  in
            let uu____11415 = FStar_TypeChecker_Env.get_range env  in
            FStar_Syntax_Syntax.mk_Tm_app uu____11352 uu____11361 uu____11415
             in
          let uu____11416 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____11416)
  
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
                  let uu____11471 =
                    FStar_TypeChecker_Env.try_lookup_lid env f  in
                  match uu____11471 with
                  | FStar_Pervasives_Native.Some uu____11486 ->
                      ((let uu____11504 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____11504
                        then
                          let uu____11508 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____11508
                        else ());
                       (let coercion =
                          let uu____11514 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____11514
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____11521 =
                            let uu____11522 =
                              let uu____11523 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____11523
                               in
                            (FStar_Pervasives_Native.None, uu____11522)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____11521
                           in
                        let e1 =
                          let uu____11527 =
                            let uu____11528 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____11528]  in
                          FStar_Syntax_Syntax.mk_Tm_app coercion2 uu____11527
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____11562 =
                          let uu____11568 =
                            let uu____11570 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____11570
                             in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____11568)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____11562);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____11589 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____11607 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____11618 -> false 
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
      let uu____11642 = FStar_Syntax_Util.head_and_args t2  in
      match uu____11642 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____11687 =
              let uu____11702 =
                let uu____11703 = FStar_Syntax_Subst.compress h1  in
                uu____11703.FStar_Syntax_Syntax.n  in
              (uu____11702, args)  in
            match uu____11687 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____11750,uu____11751) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____11784) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match
               (uu____11805,branches),uu____11807) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc  ->
                        fun br  ->
                          match acc with
                          | Yes uu____11871 -> Maybe
                          | Maybe  -> Maybe
                          | No  ->
                              let uu____11872 =
                                FStar_Syntax_Subst.open_branch br  in
                              (match uu____11872 with
                               | (uu____11873,uu____11874,br_body) ->
                                   let uu____11892 =
                                     let uu____11893 =
                                       let uu____11898 =
                                         let uu____11899 =
                                           let uu____11902 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names
                                              in
                                           FStar_All.pipe_right uu____11902
                                             FStar_Util.set_elements
                                            in
                                         FStar_All.pipe_right uu____11899
                                           (FStar_TypeChecker_Env.push_bvs
                                              env)
                                          in
                                       check_erased uu____11898  in
                                     FStar_All.pipe_right br_body uu____11893
                                      in
                                   (match uu____11892 with
                                    | No  -> No
                                    | uu____11913 -> Maybe))) No)
            | uu____11914 -> No  in
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
            (((let uu____11966 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____11966) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____11985 =
                 let uu____11986 = FStar_Syntax_Subst.compress t1  in
                 uu____11986.FStar_Syntax_Syntax.n  in
               match uu____11985 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____11991 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____12001 =
                 let uu____12002 = FStar_Syntax_Subst.compress t1  in
                 uu____12002.FStar_Syntax_Syntax.n  in
               match uu____12001 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____12007 -> false  in
             let is_type t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let t2 = FStar_Syntax_Util.unrefine t1  in
               let uu____12018 =
                 let uu____12019 = FStar_Syntax_Subst.compress t2  in
                 uu____12019.FStar_Syntax_Syntax.n  in
               match uu____12018 with
               | FStar_Syntax_Syntax.Tm_type uu____12023 -> true
               | uu____12025 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____12028 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____12028 with
             | (head,args) ->
                 ((let uu____12078 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____12078
                   then
                     let uu____12082 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____12084 = FStar_Syntax_Print.term_to_string e
                        in
                     let uu____12086 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____12088 =
                       FStar_Syntax_Print.term_to_string exp_t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____12082 uu____12084 uu____12086 uu____12088
                   else ());
                  (let mk_erased u t =
                     let uu____12106 =
                       let uu____12109 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____12109 [u]  in
                     let uu____12110 =
                       let uu____12121 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____12121]  in
                     FStar_Syntax_Util.mk_app uu____12106 uu____12110  in
                   let uu____12146 =
                     let uu____12161 =
                       let uu____12162 = FStar_Syntax_Util.un_uinst head  in
                       uu____12162.FStar_Syntax_Syntax.n  in
                     (uu____12161, args)  in
                   match uu____12146 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type exp_t)
                       ->
                       let uu____12200 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____12200 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____12240 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____12240 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____12280 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____12280 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____12320 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____12320 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____12341 ->
                       let uu____12356 =
                         let uu____12361 = check_erased env res_typ  in
                         let uu____12362 = check_erased env exp_t  in
                         (uu____12361, uu____12362)  in
                       (match uu____12356 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____12371 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____12371 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____12382 =
                                   let uu____12387 =
                                     let uu____12388 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____12388]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____12387
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____12382 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____12423 =
                              let uu____12428 =
                                let uu____12429 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____12429]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____12428
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____12423 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____12462 ->
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
        let uu____12497 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____12497 with
        | (hd,args) ->
            let uu____12546 =
              let uu____12561 =
                let uu____12562 = FStar_Syntax_Subst.compress hd  in
                uu____12562.FStar_Syntax_Syntax.n  in
              (uu____12561, args)  in
            (match uu____12546 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____12600 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun uu____12627  ->
                      FStar_Pervasives_Native.Some uu____12627) uu____12600
             | uu____12628 -> FStar_Pervasives_Native.None)
  
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
          (let uu____12681 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____12681
           then
             let uu____12684 = FStar_Syntax_Print.term_to_string e  in
             let uu____12686 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____12688 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____12684 uu____12686 uu____12688
           else ());
          (let use_eq =
             (env.FStar_TypeChecker_Env.use_eq_strict ||
                env.FStar_TypeChecker_Env.use_eq)
               ||
               (let uu____12698 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____12698 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____12723 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____12749 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____12749, false)
             else
               (let uu____12759 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____12759, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____12772) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____12784 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____12784
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1422_12800 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1422_12800.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1422_12800.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1422_12800.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard) ->
               let uu____12807 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____12807 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____12823 =
                      let uu____12824 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____12824 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____12844 =
                            let uu____12846 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____12846 = FStar_Syntax_Util.Equal  in
                          if uu____12844
                          then
                            ((let uu____12853 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____12853
                              then
                                let uu____12857 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____12859 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____12857 uu____12859
                              else ());
                             (let uu____12864 = set_result_typ c  in
                              (uu____12864, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____12871 ->
                                   true
                               | uu____12879 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____12888 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____12888
                                  in
                               let lc1 =
                                 let uu____12890 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____12891 =
                                   let uu____12892 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____12892)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____12890 uu____12891
                                  in
                               ((let uu____12896 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____12896
                                 then
                                   let uu____12900 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____12902 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____12904 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____12906 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____12900 uu____12902 uu____12904
                                     uu____12906
                                 else ());
                                (let uu____12911 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____12911 with
                                 | (c1,g_lc) ->
                                     let uu____12922 = set_result_typ c1  in
                                     let uu____12923 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____12922, uu____12923)))
                             else
                               ((let uu____12927 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____12927
                                 then
                                   let uu____12931 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____12933 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____12931 uu____12933
                                 else ());
                                (let uu____12938 = set_result_typ c  in
                                 (uu____12938, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1459_12942 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1459_12942.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1459_12942.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1459_12942.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____12952 =
                      let uu____12953 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____12953
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____12963 =
                           let uu____12964 = FStar_Syntax_Subst.compress f1
                              in
                           uu____12964.FStar_Syntax_Syntax.n  in
                         match uu____12963 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____12971,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____12973;
                                            FStar_Syntax_Syntax.vars =
                                              uu____12974;_},uu____12975)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1475_13001 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1475_13001.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1475_13001.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1475_13001.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____13002 ->
                             let uu____13003 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____13003 with
                              | (c,g_c) ->
                                  ((let uu____13015 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____13015
                                    then
                                      let uu____13019 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____13021 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____13023 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____13025 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____13019 uu____13021 uu____13023
                                        uu____13025
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
                                        let uu____13038 =
                                          let uu____13039 =
                                            FStar_Syntax_Syntax.as_arg xexp
                                             in
                                          [uu____13039]  in
                                        FStar_Syntax_Syntax.mk_Tm_app f1
                                          uu____13038
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____13066 =
                                      let uu____13071 =
                                        FStar_All.pipe_left
                                          (fun uu____13092  ->
                                             FStar_Pervasives_Native.Some
                                               uu____13092)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____13093 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____13094 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____13095 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____13071
                                        uu____13093 e uu____13094 uu____13095
                                       in
                                    match uu____13066 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1493_13103 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1493_13103.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1493_13103.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____13105 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____13105
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____13108 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____13108 with
                                         | (c2,g_lc) ->
                                             ((let uu____13120 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____13120
                                               then
                                                 let uu____13124 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____13124
                                               else ());
                                              (let uu____13129 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____13129))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_13138  ->
                              match uu___6_13138 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____13141 -> []))
                       in
                    let lc1 =
                      let uu____13143 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____13143 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1509_13145 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1509_13145.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1509_13145.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1509_13145.FStar_TypeChecker_Common.implicits)
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
        let uu____13181 =
          let uu____13184 =
            let uu____13185 =
              let uu____13194 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_Syntax_Syntax.as_arg uu____13194  in
            [uu____13185]  in
          FStar_Syntax_Syntax.mk_Tm_app ens uu____13184
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____13181  in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____13217 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____13217
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____13236 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____13252 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____13269 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____13269
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____13285)::(ens,uu____13287)::uu____13288 ->
                    let uu____13331 =
                      let uu____13334 = norm req  in
                      FStar_Pervasives_Native.Some uu____13334  in
                    let uu____13335 =
                      let uu____13336 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm uu____13336  in
                    (uu____13331, uu____13335)
                | uu____13339 ->
                    let uu____13350 =
                      let uu____13356 =
                        let uu____13358 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____13358
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____13356)
                       in
                    FStar_Errors.raise_error uu____13350
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____13378)::uu____13379 ->
                    let uu____13406 =
                      let uu____13411 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____13411
                       in
                    (match uu____13406 with
                     | (us_r,uu____13443) ->
                         let uu____13444 =
                           let uu____13449 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____13449
                            in
                         (match uu____13444 with
                          | (us_e,uu____13481) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____13484 =
                                  let uu____13485 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____13485
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____13484
                                  us_r
                                 in
                              let as_ens =
                                let uu____13487 =
                                  let uu____13488 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____13488
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____13487
                                  us_e
                                 in
                              let req =
                                let uu____13490 =
                                  let uu____13491 =
                                    let uu____13502 =
                                      FStar_Syntax_Syntax.as_arg wp  in
                                    [uu____13502]  in
                                  ((ct1.FStar_Syntax_Syntax.result_typ),
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.imp_tag))
                                    :: uu____13491
                                   in
                                FStar_Syntax_Syntax.mk_Tm_app as_req
                                  uu____13490
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____13540 =
                                  let uu____13541 =
                                    let uu____13552 =
                                      FStar_Syntax_Syntax.as_arg wp  in
                                    [uu____13552]  in
                                  ((ct1.FStar_Syntax_Syntax.result_typ),
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.imp_tag))
                                    :: uu____13541
                                   in
                                FStar_Syntax_Syntax.mk_Tm_app as_ens
                                  uu____13540
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____13589 =
                                let uu____13592 = norm req  in
                                FStar_Pervasives_Native.Some uu____13592  in
                              let uu____13593 =
                                let uu____13594 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm uu____13594  in
                              (uu____13589, uu____13593)))
                | uu____13597 -> failwith "Impossible"))
  
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
        (let uu____13636 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____13636
         then
           let uu____13641 = FStar_Syntax_Print.term_to_string tm  in
           let uu____13643 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____13641
             uu____13643
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
          (let uu____13702 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____13702
           then
             let uu____13707 = FStar_Syntax_Print.term_to_string tm  in
             let uu____13709 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____13707
               uu____13709
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____13720 =
      let uu____13722 =
        let uu____13723 = FStar_Syntax_Subst.compress t  in
        uu____13723.FStar_Syntax_Syntax.n  in
      match uu____13722 with
      | FStar_Syntax_Syntax.Tm_app uu____13727 -> false
      | uu____13745 -> true  in
    if uu____13720
    then t
    else
      (let uu____13750 = FStar_Syntax_Util.head_and_args t  in
       match uu____13750 with
       | (head,args) ->
           let uu____13793 =
             let uu____13795 =
               let uu____13796 = FStar_Syntax_Subst.compress head  in
               uu____13796.FStar_Syntax_Syntax.n  in
             match uu____13795 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____13801 -> false  in
           if uu____13793
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____13833 ->
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
          ((let uu____13880 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____13880
            then
              let uu____13883 = FStar_Syntax_Print.term_to_string e  in
              let uu____13885 = FStar_Syntax_Print.term_to_string t  in
              let uu____13887 =
                let uu____13889 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____13889
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____13883 uu____13885 uu____13887
            else ());
           (let unfolded_arrow_formals t1 =
              let rec aux bs t2 =
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf env t2  in
                let uu____13925 = FStar_Syntax_Util.arrow_formals t3  in
                match uu____13925 with
                | (bs',t4) ->
                    (match bs' with
                     | [] -> bs
                     | bs'1 -> aux (FStar_List.append bs bs'1) t4)
                 in
              aux [] t1  in
            let number_of_implicits t1 =
              let formals = unfolded_arrow_formals t1  in
              let n_implicits =
                let uu____13959 =
                  FStar_All.pipe_right formals
                    (FStar_Util.prefix_until
                       (fun uu____14037  ->
                          match uu____14037 with
                          | (uu____14045,imp) ->
                              (FStar_Option.isNone imp) ||
                                (let uu____14052 =
                                   FStar_Syntax_Util.eq_aqual imp
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Equality)
                                    in
                                 uu____14052 = FStar_Syntax_Util.Equal)))
                   in
                match uu____13959 with
                | FStar_Pervasives_Native.None  -> FStar_List.length formals
                | FStar_Pervasives_Native.Some
                    (implicits,_first_explicit,_rest) ->
                    FStar_List.length implicits
                 in
              n_implicits  in
            let inst_n_binders t1 =
              let uu____14171 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____14171 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____14185 =
                      let uu____14191 =
                        let uu____14193 = FStar_Util.string_of_int n_expected
                           in
                        let uu____14195 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____14197 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____14193 uu____14195 uu____14197
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____14191)
                       in
                    let uu____14201 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____14185 uu____14201
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_14219 =
              match uu___7_14219 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____14262 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____14262 with
                 | (bs1,c1) ->
                     let rec aux subst inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some
                          uu____14393,uu____14380) when
                           uu____14393 = Prims.int_zero ->
                           ([], bs2, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____14426,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____14428))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____14462 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____14462 with
                            | (v,uu____14503,g) ->
                                ((let uu____14518 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____14518
                                  then
                                    let uu____14521 =
                                      FStar_Syntax_Print.term_to_string v  in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____14521
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst
                                     in
                                  let uu____14531 =
                                    aux subst1 (decr_inst inst_n) rest  in
                                  match uu____14531 with
                                  | (args,bs3,subst2,g') ->
                                      let uu____14624 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____14624))))
                       | (uu____14651,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____14688 =
                             let uu____14701 =
                               let uu____14708 =
                                 let uu____14713 = FStar_Dyn.mkdyn env  in
                                 (uu____14713, tau)  in
                               FStar_Pervasives_Native.Some uu____14708  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____14701
                              in
                           (match uu____14688 with
                            | (v,uu____14746,g) ->
                                ((let uu____14761 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____14761
                                  then
                                    let uu____14764 =
                                      FStar_Syntax_Print.term_to_string v  in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____14764
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst
                                     in
                                  let uu____14774 =
                                    aux subst1 (decr_inst inst_n) rest  in
                                  match uu____14774 with
                                  | (args,bs3,subst2,g') ->
                                      let uu____14867 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____14867))))
                       | (uu____14894,bs3) ->
                           ([], bs3, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____14942 =
                       let uu____14969 = inst_n_binders t1  in
                       aux [] uu____14969 bs1  in
                     (match uu____14942 with
                      | (args,bs2,subst,guard) ->
                          (match (args, bs2) with
                           | ([],uu____15041) -> (e, torig, guard)
                           | (uu____15072,[]) when
                               let uu____15103 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____15103 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____15105 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____15133 ->
                                     FStar_Syntax_Util.arrow bs2 c1
                                  in
                               let t3 = FStar_Syntax_Subst.subst subst t2  in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               (e1, t3, guard))))
            | uu____15144 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs  ->
    let uu____15156 =
      let uu____15160 = FStar_Util.set_elements univs  in
      FStar_All.pipe_right uu____15160
        (FStar_List.map
           (fun u  ->
              let uu____15172 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____15172 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____15156 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____15200 = FStar_Util.set_is_empty x  in
      if uu____15200
      then []
      else
        (let s =
           let uu____15220 =
             let uu____15223 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____15223  in
           FStar_All.pipe_right uu____15220 FStar_Util.set_elements  in
         (let uu____15241 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____15241
          then
            let uu____15246 =
              let uu____15248 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____15248  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____15246
          else ());
         (let r =
            let uu____15257 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____15257  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____15302 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____15302
                     then
                       let uu____15307 =
                         let uu____15309 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____15309
                          in
                       let uu____15313 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____15315 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____15307 uu____15313 uu____15315
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
        let uu____15345 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____15345 FStar_Util.set_elements  in
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
        | ([],uu____15384) -> generalized_univ_names
        | (uu____15391,[]) -> explicit_univ_names
        | uu____15398 ->
            let uu____15407 =
              let uu____15413 =
                let uu____15415 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____15415
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____15413)
               in
            FStar_Errors.raise_error uu____15407 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____15437 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____15437
       then
         let uu____15442 = FStar_Syntax_Print.term_to_string t  in
         let uu____15444 = FStar_Syntax_Print.univ_names_to_string univnames
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____15442 uu____15444
       else ());
      (let univs = FStar_Syntax_Free.univs t  in
       (let uu____15453 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____15453
        then
          let uu____15458 = string_of_univs univs  in
          FStar_Util.print1 "univs to gen : %s\n" uu____15458
        else ());
       (let gen = gen_univs env univs  in
        (let uu____15467 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____15467
         then
           let uu____15472 = FStar_Syntax_Print.term_to_string t  in
           let uu____15474 = FStar_Syntax_Print.univ_names_to_string gen  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____15472 uu____15474
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
        let uu____15558 =
          let uu____15560 =
            FStar_Util.for_all
              (fun uu____15574  ->
                 match uu____15574 with
                 | (uu____15584,uu____15585,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____15560  in
        if uu____15558
        then FStar_Pervasives_Native.None
        else
          (let norm c =
             (let uu____15637 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____15637
              then
                let uu____15640 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____15640
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____15647 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____15647
               then
                 let uu____15650 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____15650
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____15668 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____15668 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____15702 =
             match uu____15702 with
             | (lbname,e,c) ->
                 let c1 = norm c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____15739 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____15739
                   then
                     let uu____15744 =
                       let uu____15746 =
                         let uu____15750 = FStar_Util.set_elements univs  in
                         FStar_All.pipe_right uu____15750
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____15746
                         (FStar_String.concat ", ")
                        in
                     let uu____15806 =
                       let uu____15808 =
                         let uu____15812 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____15812
                           (FStar_List.map
                              (fun u  ->
                                 let uu____15825 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____15827 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____15825
                                   uu____15827))
                          in
                       FStar_All.pipe_right uu____15808
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____15744
                       uu____15806
                   else ());
                  (let univs1 =
                     let uu____15841 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs1  ->
                          fun uv  ->
                            let uu____15853 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs1 uu____15853) univs
                       uu____15841
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____15860 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____15860
                    then
                      let uu____15865 =
                        let uu____15867 =
                          let uu____15871 = FStar_Util.set_elements univs1
                             in
                          FStar_All.pipe_right uu____15871
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____15867
                          (FStar_String.concat ", ")
                         in
                      let uu____15927 =
                        let uu____15929 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____15943 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____15945 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____15943
                                    uu____15945))
                           in
                        FStar_All.pipe_right uu____15929
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____15865 uu____15927
                    else ());
                   (univs1, uvs, (lbname, e, c1))))
              in
           let uu____15966 =
             let uu____15983 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____15983  in
           match uu____15966 with
           | (univs,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____16073 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____16073
                 then ()
                 else
                   (let uu____16078 = lec_hd  in
                    match uu____16078 with
                    | (lb1,uu____16086,uu____16087) ->
                        let uu____16088 = lec2  in
                        (match uu____16088 with
                         | (lb2,uu____16096,uu____16097) ->
                             let msg =
                               let uu____16100 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____16102 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____16100 uu____16102
                                in
                             let uu____16105 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____16105))
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
                 let uu____16173 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____16173
                 then ()
                 else
                   (let uu____16178 = lec_hd  in
                    match uu____16178 with
                    | (lb1,uu____16186,uu____16187) ->
                        let uu____16188 = lec2  in
                        (match uu____16188 with
                         | (lb2,uu____16196,uu____16197) ->
                             let msg =
                               let uu____16200 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____16202 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____16200 uu____16202
                                in
                             let uu____16205 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____16205))
                  in
               let lecs1 =
                 let uu____16216 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____16269 = univs_and_uvars_of_lec this_lec  in
                        match uu____16269 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____16216 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail rng k =
                   let uu____16379 = lec_hd  in
                   match uu____16379 with
                   | (lbname,e,c) ->
                       let uu____16389 =
                         let uu____16395 =
                           let uu____16397 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____16399 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____16401 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____16397 uu____16399 uu____16401
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____16395)
                          in
                       FStar_Errors.raise_error uu____16389 rng
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____16423 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____16423 with
                         | FStar_Pervasives_Native.Some uu____16432 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____16440 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____16444 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____16444 with
                              | (bs,kres) ->
                                  ((let uu____16464 =
                                      let uu____16465 =
                                        let uu____16468 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____16468
                                         in
                                      uu____16465.FStar_Syntax_Syntax.n  in
                                    match uu____16464 with
                                    | FStar_Syntax_Syntax.Tm_type uu____16469
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____16473 =
                                          let uu____16475 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____16475  in
                                        if uu____16473
                                        then
                                          fail
                                            u.FStar_Syntax_Syntax.ctx_uvar_range
                                            kres
                                        else ()
                                    | uu____16480 ->
                                        fail
                                          u.FStar_Syntax_Syntax.ctx_uvar_range
                                          kres);
                                   (let a =
                                      let uu____16482 =
                                        let uu____16485 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun uu____16488  ->
                                             FStar_Pervasives_Native.Some
                                               uu____16488) uu____16485
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____16482
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____16496 ->
                                          let uu____16497 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____16497
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
                      (fun uu____16600  ->
                         match uu____16600 with
                         | (lbname,e,c) ->
                             let uu____16646 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____16707 ->
                                   let uu____16720 = (e, c)  in
                                   (match uu____16720 with
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
                                                (fun uu____16760  ->
                                                   match uu____16760 with
                                                   | (x,uu____16766) ->
                                                       let uu____16767 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____16767)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____16785 =
                                                let uu____16787 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____16787
                                                 in
                                              if uu____16785
                                              then
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  tm tvar_args
                                                  tm.FStar_Syntax_Syntax.pos
                                              else tm  in
                                            FStar_Syntax_InstFV.inst
                                              instantiate_lbname_with_app e1
                                          else e1  in
                                        let t =
                                          let uu____16796 =
                                            let uu____16797 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____16797.FStar_Syntax_Syntax.n
                                             in
                                          match uu____16796 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____16822 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____16822 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____16833 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____16837 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____16837, gen_tvars))
                                in
                             (match uu____16646 with
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
        (let uu____16984 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____16984
         then
           let uu____16987 =
             let uu____16989 =
               FStar_List.map
                 (fun uu____17004  ->
                    match uu____17004 with
                    | (lb,uu____17013,uu____17014) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____16989 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____16987
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____17040  ->
                match uu____17040 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____17069 = gen env is_rec lecs  in
           match uu____17069 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____17168  ->
                       match uu____17168 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____17230 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____17230
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____17278  ->
                           match uu____17278 with
                           | (l,us,e,c,gvs) ->
                               let uu____17312 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____17314 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____17316 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____17318 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____17320 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____17312 uu____17314 uu____17316
                                 uu____17318 uu____17320))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames  ->
              fun uu____17365  ->
                match uu____17365 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____17409 =
                      check_universe_generalization univnames
                        generalized_univs t
                       in
                    (l, uu____17409, t, c, gvs)) univnames_lecs
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
        let uu____17464 =
          let uu____17468 =
            let uu____17470 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____17470  in
          FStar_Pervasives_Native.Some uu____17468  in
        FStar_Profiling.profile
          (fun uu____17487  -> generalize' env is_rec lecs) uu____17464
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
              let uu____17544 =
                FStar_TypeChecker_Rel.get_teq_predicate env2 t1 t21  in
              match uu____17544 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some f ->
                  let uu____17550 = FStar_TypeChecker_Env.apply_guard f e  in
                  FStar_All.pipe_right uu____17550
                    (fun uu____17553  ->
                       FStar_Pervasives_Native.Some uu____17553)
            else
              if env2.FStar_TypeChecker_Env.use_eq
              then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
              else
                (let uu____17562 =
                   FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                    in
                 match uu____17562 with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some f ->
                     let uu____17568 = FStar_TypeChecker_Env.apply_guard f e
                        in
                     FStar_All.pipe_left
                       (fun uu____17571  ->
                          FStar_Pervasives_Native.Some uu____17571)
                       uu____17568)
             in
          let uu____17572 = maybe_coerce_lc env1 e lc t2  in
          match uu____17572 with
          | (e1,lc1,g_c) ->
              let uu____17588 =
                check env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____17588 with
               | FStar_Pervasives_Native.None  ->
                   let uu____17597 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____17603 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____17597 uu____17603
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____17612 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____17612
                     then
                       let uu____17617 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____17617
                     else ());
                    (let uu____17623 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (e1, lc1, uu____17623))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____17651 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____17651
         then
           let uu____17654 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____17654
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____17668 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____17668 with
         | (c,g_c) ->
             let uu____17680 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____17680
             then
               let uu____17688 =
                 let uu____17690 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____17690  in
               (uu____17688, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____17698 =
                    let uu____17699 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____17699
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____17698
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____17700 = check_trivial_precondition env c1  in
                match uu____17700 with
                | (ct,vc,g_pre) ->
                    ((let uu____17716 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____17716
                      then
                        let uu____17721 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____17721
                      else ());
                     (let uu____17726 =
                        let uu____17728 =
                          let uu____17729 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____17729  in
                        discharge uu____17728  in
                      let uu____17730 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____17726, uu____17730)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head  ->
    fun seen_args  ->
      let short_bin_op f uu___8_17764 =
        match uu___8_17764 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst,uu____17774)::[] -> f fst
        | uu____17799 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____17811 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____17811
          (fun uu____17812  ->
             FStar_TypeChecker_Common.NonTrivial uu____17812)
         in
      let op_or_e e =
        let uu____17823 =
          let uu____17824 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____17824  in
        FStar_All.pipe_right uu____17823
          (fun uu____17827  ->
             FStar_TypeChecker_Common.NonTrivial uu____17827)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun uu____17834  ->
             FStar_TypeChecker_Common.NonTrivial uu____17834)
         in
      let op_or_t t =
        let uu____17845 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____17845
          (fun uu____17848  ->
             FStar_TypeChecker_Common.NonTrivial uu____17848)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun uu____17855  ->
             FStar_TypeChecker_Common.NonTrivial uu____17855)
         in
      let short_op_ite uu___9_17861 =
        match uu___9_17861 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____17871)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____17898)::[] ->
            let uu____17939 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____17939
              (fun uu____17940  ->
                 FStar_TypeChecker_Common.NonTrivial uu____17940)
        | uu____17941 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____17953 =
          let uu____17961 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____17961)  in
        let uu____17969 =
          let uu____17979 =
            let uu____17987 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____17987)  in
          let uu____17995 =
            let uu____18005 =
              let uu____18013 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____18013)  in
            let uu____18021 =
              let uu____18031 =
                let uu____18039 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____18039)  in
              let uu____18047 =
                let uu____18057 =
                  let uu____18065 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____18065)  in
                [uu____18057; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____18031 :: uu____18047  in
            uu____18005 :: uu____18021  in
          uu____17979 :: uu____17995  in
        uu____17953 :: uu____17969  in
      match head.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____18127 =
            FStar_Util.find_map table
              (fun uu____18142  ->
                 match uu____18142 with
                 | (x,mk) ->
                     let uu____18159 = FStar_Ident.lid_equals x lid  in
                     if uu____18159
                     then
                       let uu____18164 = mk seen_args  in
                       FStar_Pervasives_Native.Some uu____18164
                     else FStar_Pervasives_Native.None)
             in
          (match uu____18127 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____18168 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____18176 =
      let uu____18177 = FStar_Syntax_Util.un_uinst l  in
      uu____18177.FStar_Syntax_Syntax.n  in
    match uu____18176 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____18182 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd,uu____18218)::uu____18219 -> FStar_Syntax_Syntax.range_of_bv hd
        | uu____18238 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____18247,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____18248))::uu____18249 -> bs
      | uu____18267 ->
          let uu____18268 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____18268 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____18272 =
                 let uu____18273 = FStar_Syntax_Subst.compress t  in
                 uu____18273.FStar_Syntax_Syntax.n  in
               (match uu____18272 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____18277) ->
                    let uu____18298 =
                      FStar_Util.prefix_until
                        (fun uu___10_18338  ->
                           match uu___10_18338 with
                           | (uu____18346,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____18347)) ->
                               false
                           | uu____18352 -> true) bs'
                       in
                    (match uu____18298 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____18388,uu____18389) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____18461,uu____18462) ->
                         let uu____18535 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____18556  ->
                                   match uu____18556 with
                                   | (x,uu____18565) ->
                                       let uu____18570 =
                                         FStar_Ident.string_of_id
                                           x.FStar_Syntax_Syntax.ppname
                                          in
                                       FStar_Util.starts_with uu____18570 "'"))
                            in
                         if uu____18535
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____18616  ->
                                     match uu____18616 with
                                     | (x,i) ->
                                         let uu____18635 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____18635, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____18646 -> bs))
  
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
            let uu____18675 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____18675
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
          let uu____18706 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____18706
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
        (let uu____18749 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____18749
         then
           ((let uu____18754 = FStar_Ident.string_of_lid lident  in
             d uu____18754);
            (let uu____18756 = FStar_Ident.string_of_lid lident  in
             let uu____18758 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____18756 uu____18758))
         else ());
        (let fv =
           let uu____18764 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____18764
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
         let uu____18776 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Range.dummyRange
            in
         ((let uu___2131_18778 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2131_18778.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2131_18778.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2131_18778.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2131_18778.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2131_18778.FStar_Syntax_Syntax.sigopts)
           }), uu____18776))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_18796 =
        match uu___11_18796 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____18799 -> false  in
      let reducibility uu___12_18807 =
        match uu___12_18807 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____18814 -> false  in
      let assumption uu___13_18822 =
        match uu___13_18822 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____18826 -> false  in
      let reification uu___14_18834 =
        match uu___14_18834 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____18837 -> true
        | uu____18839 -> false  in
      let inferred uu___15_18847 =
        match uu___15_18847 with
        | FStar_Syntax_Syntax.Discriminator uu____18849 -> true
        | FStar_Syntax_Syntax.Projector uu____18851 -> true
        | FStar_Syntax_Syntax.RecordType uu____18857 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____18867 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____18880 -> false  in
      let has_eq uu___16_18888 =
        match uu___16_18888 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____18892 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____18971 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____18978 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____19011 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____19011))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____19042 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____19042
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
           | FStar_Syntax_Syntax.Sig_bundle uu____19062 ->
               let uu____19071 =
                 let uu____19073 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_19079  ->
                           match uu___17_19079 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____19082 -> false))
                    in
                 Prims.op_Negation uu____19073  in
               if uu____19071
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____19089 -> ()
           | FStar_Syntax_Syntax.Sig_fail uu____19096 -> ()
           | uu____19109 ->
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
      let uu____19123 =
        let uu____19125 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_19131  ->
                  match uu___18_19131 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____19134 -> false))
           in
        FStar_All.pipe_right uu____19125 Prims.op_Negation  in
      if uu____19123
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____19155 =
            let uu____19161 =
              let uu____19163 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____19163 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____19161)  in
          FStar_Errors.raise_error uu____19155 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____19181 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____19189 =
            let uu____19191 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____19191  in
          if uu____19189 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____19202),uu____19203) ->
              ((let uu____19215 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____19215
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____19224 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____19224
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____19235 ->
              ((let uu____19245 =
                  let uu____19247 =
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
                  Prims.op_Negation uu____19247  in
                if uu____19245 then err'1 () else ());
               (let uu____19257 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_19263  ->
                           match uu___19_19263 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____19266 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____19257
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____19272 ->
              let uu____19279 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____19279 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____19287 ->
              let uu____19294 =
                let uu____19296 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____19296  in
              if uu____19294 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____19306 ->
              let uu____19307 =
                let uu____19309 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____19309  in
              if uu____19307 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19319 ->
              let uu____19332 =
                let uu____19334 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____19334  in
              if uu____19332 then err'1 () else ()
          | uu____19344 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____19383 =
          let uu____19384 = FStar_Syntax_Subst.compress t1  in
          uu____19384.FStar_Syntax_Syntax.n  in
        match uu____19383 with
        | FStar_Syntax_Syntax.Tm_arrow uu____19388 ->
            let uu____19403 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____19403 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____19412;
               FStar_Syntax_Syntax.index = uu____19413;
               FStar_Syntax_Syntax.sort = t2;_},uu____19415)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head,uu____19424) -> descend env head
        | FStar_Syntax_Syntax.Tm_uinst (head,uu____19450) -> descend env head
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____19456 -> false
      
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
        (let uu____19466 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____19466
         then
           let uu____19471 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____19471
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
                  let uu____19536 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____19536 r  in
                let uu____19546 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____19546 with
                | (uu____19555,signature) ->
                    let uu____19557 =
                      let uu____19558 = FStar_Syntax_Subst.compress signature
                         in
                      uu____19558.FStar_Syntax_Syntax.n  in
                    (match uu____19557 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____19566) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____19614 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____19630 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____19632 =
                                       FStar_Ident.string_of_lid eff_name  in
                                     let uu____19634 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____19630 uu____19632 uu____19634) r
                                 in
                              (match uu____19614 with
                               | (is,g) ->
                                   let uu____19647 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____19649 =
                                             let uu____19650 =
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
                                                 = uu____19650;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____19649
                                            in
                                         let uu____19669 =
                                           let uu____19670 =
                                             let uu____19685 =
                                               let uu____19694 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   FStar_Syntax_Syntax.t_unit
                                                  in
                                               [uu____19694]  in
                                             (uu____19685, eff_c)  in
                                           FStar_Syntax_Syntax.Tm_arrow
                                             uu____19670
                                            in
                                         FStar_Syntax_Syntax.mk uu____19669 r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____19725 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____19725
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____19734 =
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg (a_tm
                                             :: is)
                                            in
                                         FStar_Syntax_Syntax.mk_Tm_app repr
                                           uu____19734 r
                                      in
                                   (uu____19647, g))
                          | uu____19743 -> fail signature)
                     | uu____19744 -> fail signature)
  
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
            let uu____19775 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____19775
              (fun ed  ->
                 let uu____19783 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____19783 u a_tm)
  
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
              let uu____19819 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____19819 with
              | (uu____19824,sig_tm) ->
                  let fail t =
                    let uu____19832 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____19832 r  in
                  let uu____19838 =
                    let uu____19839 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____19839.FStar_Syntax_Syntax.n  in
                  (match uu____19838 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____19843) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____19866)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____19888 -> fail sig_tm)
                   | uu____19889 -> fail sig_tm)
  
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
          (let uu____19920 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____19920
           then
             let uu____19925 = FStar_Syntax_Print.comp_to_string c  in
             let uu____19927 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____19925 uu____19927
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____19934 =
             let uu____19945 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____19946 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____19945, (ct.FStar_Syntax_Syntax.result_typ), uu____19946)
              in
           match uu____19934 with
           | (u,a,c_is) ->
               let uu____19994 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____19994 with
                | (uu____20003,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____20014 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____20016 = FStar_Ident.string_of_lid tgt  in
                      let uu____20018 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____20014 uu____20016 s uu____20018
                       in
                    let uu____20021 =
                      let uu____20054 =
                        let uu____20055 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____20055.FStar_Syntax_Syntax.n  in
                      match uu____20054 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____20119 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____20119 with
                           | (a_b::bs1,c2) ->
                               let uu____20179 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               (a_b, uu____20179, c2))
                      | uu____20267 ->
                          let uu____20268 =
                            let uu____20274 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____20274)
                             in
                          FStar_Errors.raise_error uu____20268 r
                       in
                    (match uu____20021 with
                     | (a_b,(rest_bs,f_b::[]),lift_c) ->
                         let uu____20392 =
                           let uu____20399 =
                             let uu____20400 =
                               let uu____20401 =
                                 let uu____20408 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____20408, a)  in
                               FStar_Syntax_Syntax.NT uu____20401  in
                             [uu____20400]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____20399
                             (fun b  ->
                                let uu____20425 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____20427 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____20429 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____20431 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____20425 uu____20427 uu____20429
                                  uu____20431) r
                            in
                         (match uu____20392 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____20445 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____20445
                                then
                                  let uu____20450 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____20459 =
                                             let uu____20461 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____20461
                                              in
                                           Prims.op_Hat s uu____20459) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____20450
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____20492 =
                                           let uu____20499 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____20499, t)  in
                                         FStar_Syntax_Syntax.NT uu____20492)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____20518 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____20518
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____20524 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
                                    effect_args_from_repr f_sort uu____20524
                                      r
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____20533 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____20533)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let lift_ct =
                                  let uu____20535 =
                                    FStar_All.pipe_right lift_c
                                      (FStar_Syntax_Subst.subst_comp substs)
                                     in
                                  FStar_All.pipe_right uu____20535
                                    FStar_Syntax_Util.comp_to_comp_typ
                                   in
                                let is =
                                  let uu____20539 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____20539 r
                                   in
                                let fml =
                                  let uu____20544 =
                                    let uu____20549 =
                                      FStar_List.hd
                                        lift_ct.FStar_Syntax_Syntax.comp_univs
                                       in
                                    let uu____20550 =
                                      let uu____20551 =
                                        FStar_List.hd
                                          lift_ct.FStar_Syntax_Syntax.effect_args
                                         in
                                      FStar_Pervasives_Native.fst uu____20551
                                       in
                                    (uu____20549, uu____20550)  in
                                  match uu____20544 with
                                  | (u1,wp) ->
                                      FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                        env u1
                                        lift_ct.FStar_Syntax_Syntax.result_typ
                                        wp FStar_Range.dummyRange
                                   in
                                (let uu____20577 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects"))
                                     &&
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme)
                                    in
                                 if uu____20577
                                 then
                                   let uu____20583 =
                                     FStar_Syntax_Print.term_to_string fml
                                      in
                                   FStar_Util.print1 "Guard for lift is: %s"
                                     uu____20583
                                 else ());
                                (let c1 =
                                   let uu____20589 =
                                     let uu____20590 =
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
                                         uu____20590;
                                       FStar_Syntax_Syntax.flags = []
                                     }  in
                                   FStar_Syntax_Syntax.mk_Comp uu____20589
                                    in
                                 (let uu____20614 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects")
                                     in
                                  if uu____20614
                                  then
                                    let uu____20619 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    FStar_Util.print1 "} Lifted comp: %s\n"
                                      uu____20619
                                  else ());
                                 (let uu____20624 =
                                    let uu____20625 =
                                      FStar_TypeChecker_Env.conj_guard g
                                        guard_f
                                       in
                                    let uu____20626 =
                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                        (FStar_TypeChecker_Common.NonTrivial
                                           fml)
                                       in
                                    FStar_TypeChecker_Env.conj_guard
                                      uu____20625 uu____20626
                                     in
                                  (c1, uu____20624)))))))))
  
let lift_tf_layered_effect_term :
  'uuuuuu20640 .
    'uuuuuu20640 ->
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
              let uu____20669 =
                let uu____20674 =
                  FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____20674
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____20669 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____20717 =
                let uu____20718 =
                  let uu____20721 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____20721
                    FStar_Syntax_Subst.compress
                   in
                uu____20718.FStar_Syntax_Syntax.n  in
              match uu____20717 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____20744::bs,uu____20746)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____20786 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____20786
                    FStar_Pervasives_Native.fst
              | uu____20892 ->
                  let uu____20893 =
                    let uu____20899 =
                      let uu____20901 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____20901
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____20899)  in
                  FStar_Errors.raise_error uu____20893
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____20928 = FStar_Syntax_Syntax.as_arg a  in
              let uu____20937 =
                let uu____20948 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____20984  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____20991 =
                  let uu____21002 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____21002]  in
                FStar_List.append uu____20948 uu____20991  in
              uu____20928 :: uu____20937  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              e.FStar_Syntax_Syntax.pos
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index  ->
        let uu____21073 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____21073 with
        | (uu____21078,t) ->
            let err n =
              let uu____21088 =
                let uu____21094 =
                  let uu____21096 = FStar_Ident.string_of_lid datacon  in
                  let uu____21098 = FStar_Util.string_of_int n  in
                  let uu____21100 = FStar_Util.string_of_int index  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____21096 uu____21098 uu____21100
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____21094)
                 in
              let uu____21104 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____21088 uu____21104  in
            let uu____21105 =
              let uu____21106 = FStar_Syntax_Subst.compress t  in
              uu____21106.FStar_Syntax_Syntax.n  in
            (match uu____21105 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____21110) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____21165  ->
                           match uu____21165 with
                           | (uu____21173,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____21182 -> true)))
                    in
                 if (FStar_List.length bs1) <= index
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index  in
                    FStar_Syntax_Util.mk_field_projector_name datacon
                      (FStar_Pervasives_Native.fst b) index)
             | uu____21216 -> err Prims.int_zero)
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub  ->
      let uu____21229 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub.FStar_Syntax_Syntax.target)
         in
      if uu____21229
      then
        let uu____21232 =
          let uu____21245 =
            FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub.FStar_Syntax_Syntax.target uu____21245
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____21232;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____21280 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____21280 with
           | (uu____21289,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____21308 =
                 let uu____21309 =
                   let uu___2507_21310 = ct  in
                   let uu____21311 =
                     let uu____21322 =
                       let uu____21331 =
                         let uu____21332 =
                           let uu____21333 =
                             let uu____21350 =
                               let uu____21361 =
                                 FStar_Syntax_Syntax.as_arg
                                   ct.FStar_Syntax_Syntax.result_typ
                                  in
                               [uu____21361; wp]  in
                             (lift_t, uu____21350)  in
                           FStar_Syntax_Syntax.Tm_app uu____21333  in
                         FStar_Syntax_Syntax.mk uu____21332
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____21331
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____21322]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2507_21310.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2507_21310.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____21311;
                     FStar_Syntax_Syntax.flags =
                       (uu___2507_21310.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____21309  in
               (uu____21308, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____21461 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____21461 with
           | (uu____21468,lift_t) ->
               let uu____21470 =
                 let uu____21471 =
                   let uu____21488 =
                     let uu____21499 = FStar_Syntax_Syntax.as_arg r  in
                     let uu____21508 =
                       let uu____21519 =
                         FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                          in
                       let uu____21528 =
                         let uu____21539 = FStar_Syntax_Syntax.as_arg e  in
                         [uu____21539]  in
                       uu____21519 :: uu____21528  in
                     uu____21499 :: uu____21508  in
                   (lift_t, uu____21488)  in
                 FStar_Syntax_Syntax.Tm_app uu____21471  in
               FStar_Syntax_Syntax.mk uu____21470 e.FStar_Syntax_Syntax.pos
            in
         let uu____21592 =
           let uu____21605 =
             FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____21605 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____21592;
           FStar_TypeChecker_Env.mlift_term =
             (match sub.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____21641  ->
                        fun uu____21642  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun sub  ->
      let uu____21665 = get_mlift_for_subeff env sub  in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub.FStar_Syntax_Syntax.source sub.FStar_Syntax_Syntax.target
        uu____21665
  
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
  