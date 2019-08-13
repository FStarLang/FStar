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
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun xs  ->
      fun g  ->
        let uu____84 =
          let uu____86 = FStar_Options.eager_subtyping ()  in
          FStar_All.pipe_left Prims.op_Negation uu____86  in
        if uu____84
        then g
        else
          (let uu____93 =
             FStar_All.pipe_right g.FStar_TypeChecker_Common.deferred
               (FStar_List.partition
                  (fun uu____145  ->
                     match uu____145 with
                     | (uu____152,p) ->
                         FStar_TypeChecker_Rel.flex_prob_closing env xs p))
              in
           match uu____93 with
           | (solve_now,defer) ->
               ((let uu____187 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____187
                 then
                   (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                    FStar_List.iter
                      (fun uu____204  ->
                         match uu____204 with
                         | (s,p) ->
                             let uu____214 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____214)
                      solve_now;
                    FStar_Util.print_string " ...DEFERRED THE REST:\n";
                    FStar_List.iter
                      (fun uu____229  ->
                         match uu____229 with
                         | (s,p) ->
                             let uu____239 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____239) defer;
                    FStar_Util.print_string "END\n")
                 else ());
                (let g1 =
                   FStar_TypeChecker_Rel.solve_deferred_constraints env
                     (let uu___46_247 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          (uu___46_247.FStar_TypeChecker_Common.guard_f);
                        FStar_TypeChecker_Common.deferred = solve_now;
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___46_247.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___46_247.FStar_TypeChecker_Common.implicits)
                      })
                    in
                 let g2 =
                   let uu___49_249 = g1  in
                   {
                     FStar_TypeChecker_Common.guard_f =
                       (uu___49_249.FStar_TypeChecker_Common.guard_f);
                     FStar_TypeChecker_Common.deferred = defer;
                     FStar_TypeChecker_Common.univ_ineqs =
                       (uu___49_249.FStar_TypeChecker_Common.univ_ineqs);
                     FStar_TypeChecker_Common.implicits =
                       (uu___49_249.FStar_TypeChecker_Common.implicits)
                   }  in
                 g2)))
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____264 =
        let uu____266 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____266  in
      if uu____264
      then
        let us =
          let uu____271 =
            let uu____275 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____275
             in
          FStar_All.pipe_right uu____271 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____294 =
            let uu____300 =
              let uu____302 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____302
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____300)  in
          FStar_Errors.log_issue r uu____294);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool))
  =
  fun env  ->
    fun uu____325  ->
      match uu____325 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____336;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____338;
          FStar_Syntax_Syntax.lbpos = uu____339;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____374 = FStar_Syntax_Subst.open_univ_vars univ_vars1 e
                  in
               (match uu____374 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____412) -> aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____419) ->
                          FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____474) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____510 = FStar_Options.ml_ish ()  in
                                if uu____510
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____532 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____532
                            then
                              let uu____535 = FStar_Range.string_of_range r
                                 in
                              let uu____537 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____535 uu____537
                            else ());
                           FStar_Util.Inl t2)
                      | uu____542 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____544 = aux e1  in
                      match uu____544 with
                      | FStar_Util.Inr c ->
                          let uu____550 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____550
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____555 =
                               let uu____561 =
                                 let uu____563 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____563
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____561)
                                in
                             FStar_Errors.raise_error uu____555 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars2, t2, true))
           | uu____572 ->
               let uu____573 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____573 with
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
    let pat_as_arg uu____637 =
      match uu____637 with
      | (p,i) ->
          let uu____657 = decorated_pattern_as_term p  in
          (match uu____657 with
           | (vars,te) ->
               let uu____680 =
                 let uu____685 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____685)  in
               (vars, uu____680))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____699 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____699)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____703 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____703)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____707 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____707)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____730 =
          let uu____749 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____749 FStar_List.unzip  in
        (match uu____730 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____887 =
               let uu____888 =
                 let uu____889 =
                   let uu____906 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____906, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____889  in
               mk1 uu____888  in
             (vars1, uu____887))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____945,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____955,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____969 -> FStar_Pervasives_Native.Some hd1)
  
let (lcomp_univ_opt :
  FStar_TypeChecker_Common.lcomp ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun lc  ->
    let uu____980 =
      FStar_All.pipe_right lc FStar_TypeChecker_Common.lcomp_comp  in
    FStar_All.pipe_right uu____980 comp_univ_opt
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____1009)::[] -> wp
      | uu____1034 ->
          let uu____1045 =
            let uu____1047 =
              let uu____1049 =
                FStar_List.map
                  (fun uu____1063  ->
                     match uu____1063 with
                     | (x,uu____1072) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____1049 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____1047
             in
          failwith uu____1045
       in
    let uu____1083 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____1083, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____1100 = destruct_comp c  in
        match uu____1100 with
        | (u,uu____1108,wp) ->
            let uu____1110 =
              let uu____1121 =
                let uu____1130 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____1130  in
              [uu____1121]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____1110;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____1163 =
          let uu____1170 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____1171 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____1170 uu____1171  in
        match uu____1163 with | (m,uu____1173,uu____1174) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____1191 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2)
           in
        if uu____1191
        then FStar_Parser_Const.effect_Tot_lid
        else
          join_effects env c1.FStar_TypeChecker_Common.eff_name
            c2.FStar_TypeChecker_Common.eff_name
  
let (lift_and_destruct :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv *
          FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.universe *
          FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) *
          (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
          FStar_Syntax_Syntax.typ)))
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let c11 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
        let c21 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
        let uu____1238 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____1238 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____1275 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____1275 with
             | (a,kwp) ->
                 let uu____1306 = destruct_comp m1  in
                 let uu____1313 = destruct_comp m2  in
                 ((md, a, kwp), uu____1306, uu____1313))
  
let (lift_to_layered_effect :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c  ->
      fun eff_name  ->
        let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
        let uu____1363 =
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name eff_name
           in
        if uu____1363
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let src_ed =
             FStar_TypeChecker_Env.get_effect_decl env
               ct.FStar_Syntax_Syntax.effect_name
              in
           let dst_ed = FStar_TypeChecker_Env.get_effect_decl env eff_name
              in
           if
             src_ed.FStar_Syntax_Syntax.is_layered ||
               (Prims.op_Negation dst_ed.FStar_Syntax_Syntax.is_layered)
           then
             failwith
               "lift_to_layered_effect called with layered src or non-layered dst"
           else ();
           (let lift_t =
              let uu____1380 =
                FStar_TypeChecker_Env.monad_leq env
                  src_ed.FStar_Syntax_Syntax.mname
                  dst_ed.FStar_Syntax_Syntax.mname
                 in
              match uu____1380 with
              | FStar_Pervasives_Native.None  ->
                  failwith
                    (Prims.op_Hat "Could not find an edge from "
                       (Prims.op_Hat
                          (src_ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          (Prims.op_Hat " to "
                             (dst_ed.FStar_Syntax_Syntax.mname).FStar_Ident.str)))
              | FStar_Pervasives_Native.Some lift ->
                  FStar_All.pipe_right
                    (lift.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_t
                    FStar_Util.must
               in
            let uu____1388 = destruct_comp ct  in
            match uu____1388 with
            | (u,a,wp) ->
                let uu____1402 =
                  FStar_TypeChecker_Env.inst_tscheme_with lift_t [u]  in
                (match uu____1402 with
                 | (uu____1411,lift_t1) ->
                     let uu____1413 =
                       let uu____1426 =
                         let uu____1427 = FStar_Syntax_Subst.compress lift_t1
                            in
                         uu____1427.FStar_Syntax_Syntax.n  in
                       match uu____1426 with
                       | FStar_Syntax_Syntax.Tm_arrow (bs,c1) ->
                           let uu____1464 =
                             FStar_Syntax_Subst.open_comp bs c1  in
                           FStar_All.pipe_right uu____1464
                             (fun uu____1481  ->
                                match uu____1481 with
                                | (bs1,c2) ->
                                    let uu____1492 =
                                      FStar_Syntax_Util.comp_to_comp_typ c2
                                       in
                                    (bs1, uu____1492))
                       | uu____1493 ->
                           let uu____1494 =
                             let uu____1496 =
                               let uu____1498 =
                                 FStar_Syntax_Print.term_to_string lift_t1
                                  in
                               Prims.op_Hat uu____1498
                                 " is not an arrow type"
                                in
                             Prims.op_Hat "lift_t: " uu____1496  in
                           failwith uu____1494
                        in
                     (match uu____1413 with
                      | (lift_bs,lift_ct) ->
                          let uu____1536 =
                            match lift_bs with
                            | a_b::wp_b::bs when
                                (FStar_List.length bs) >= Prims.int_one ->
                                let uu____1631 =
                                  let uu____1640 =
                                    FStar_List.splitAt
                                      ((FStar_List.length bs) - Prims.int_one)
                                      bs
                                     in
                                  FStar_All.pipe_right uu____1640
                                    FStar_Pervasives_Native.fst
                                   in
                                (a_b, wp_b, uu____1631)
                            | uu____1738 ->
                                let uu____1747 =
                                  let uu____1749 =
                                    let uu____1751 =
                                      FStar_Syntax_Print.term_to_string
                                        lift_t1
                                       in
                                    Prims.op_Hat uu____1751
                                      " does not have enough binders"
                                     in
                                  Prims.op_Hat "lift_t: " uu____1749  in
                                failwith uu____1747
                             in
                          (match uu____1536 with
                           | (a_b,wp_b,rest_bs) ->
                               let uu____1828 =
                                 let uu____1835 =
                                   let uu____1836 =
                                     FStar_Syntax_Subst.compress
                                       lift_ct.FStar_Syntax_Syntax.result_typ
                                      in
                                   uu____1836.FStar_Syntax_Syntax.n  in
                                 match uu____1835 with
                                 | FStar_Syntax_Syntax.Tm_app
                                     (uu____1845,uu____1846::is) ->
                                     let uu____1888 =
                                       FStar_List.map
                                         FStar_Pervasives_Native.fst is
                                        in
                                     ((lift_ct.FStar_Syntax_Syntax.comp_univs),
                                       uu____1888)
                                 | uu____1905 ->
                                     let uu____1906 =
                                       let uu____1908 =
                                         let uu____1910 =
                                           FStar_Syntax_Print.term_to_string
                                             lift_t1
                                            in
                                         Prims.op_Hat uu____1910
                                           " does not have a repr return type"
                                          in
                                       Prims.op_Hat "lift_t: " uu____1908  in
                                     failwith uu____1906
                                  in
                               (match uu____1828 with
                                | (u_m,is) ->
                                    let uu____1930 =
                                      let uu____1939 =
                                        let uu____1948 =
                                          let uu____1957 =
                                            FStar_TypeChecker_Env.push_binders
                                              env [a_b; wp_b]
                                             in
                                          (uu____1957, [],
                                            FStar_TypeChecker_Env.trivial_guard)
                                           in
                                        FStar_List.fold_left
                                          (fun uu____2003  ->
                                             fun b  ->
                                               match uu____2003 with
                                               | (env1,is_uvars,g) ->
                                                   let uu____2034 =
                                                     FStar_TypeChecker_Env.new_implicit_var_aux
                                                       ""
                                                       FStar_Range.dummyRange
                                                       env1
                                                       (FStar_Pervasives_Native.fst
                                                          b).FStar_Syntax_Syntax.sort
                                                       FStar_Syntax_Syntax.Strict
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   (match uu____2034 with
                                                    | (t,uu____2063,g_t) ->
                                                        let uu____2077 =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env1 [b]
                                                           in
                                                        let uu____2090 =
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g g_t
                                                           in
                                                        (uu____2077,
                                                          (FStar_List.append
                                                             is_uvars 
                                                             [t]),
                                                          uu____2090)))
                                          uu____1948 rest_bs
                                         in
                                      match uu____1939 with
                                      | (uu____2101,rest_bs_uvars,g) ->
                                          (rest_bs_uvars, g)
                                       in
                                    (match uu____1930 with
                                     | (rest_bs_uvars,g) ->
                                         let subst_for_is =
                                           FStar_List.map2
                                             (fun b  ->
                                                fun t  ->
                                                  let uu____2150 =
                                                    let uu____2157 =
                                                      FStar_All.pipe_right b
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    (uu____2157, t)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____2150) (a_b :: wp_b
                                             :: rest_bs) (a :: wp ::
                                             rest_bs_uvars)
                                            in
                                         let is1 =
                                           FStar_List.map
                                             (FStar_Syntax_Subst.subst
                                                subst_for_is) is
                                            in
                                         let uu____2187 =
                                           let uu____2188 =
                                             let uu____2189 =
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 is1
                                                in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = u_m;
                                               FStar_Syntax_Syntax.effect_name
                                                 = eff_name;
                                               FStar_Syntax_Syntax.result_typ
                                                 = a;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____2189;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____2188
                                            in
                                         (uu____2187, g))))))))
  
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
            let uu____2268 =
              let uu____2269 =
                let uu____2280 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____2280]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____2269;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____2268
  
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
          let uu____2364 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____2364
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2376 =
      let uu____2377 = FStar_Syntax_Subst.compress t  in
      uu____2377.FStar_Syntax_Syntax.n  in
    match uu____2376 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2381 -> true
    | uu____2397 -> false
  
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
              let uu____2467 =
                let uu____2469 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____2469  in
              if uu____2467
              then f
              else (let uu____2476 = reason1 ()  in label uu____2476 r f)
  
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
            let uu___311_2497 = g  in
            let uu____2498 =
              let uu____2499 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____2499  in
            {
              FStar_TypeChecker_Common.guard_f = uu____2498;
              FStar_TypeChecker_Common.deferred =
                (uu___311_2497.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___311_2497.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___311_2497.FStar_TypeChecker_Common.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2520 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____2520
        then c
        else
          (let uu____2525 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____2525
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let uu____2566 =
                  FStar_Syntax_Util.get_match_with_close_wps
                    md.FStar_Syntax_Syntax.match_wps
                   in
                match uu____2566 with
                | (uu____2575,uu____2576,close1) ->
                    FStar_List.fold_right
                      (fun x  ->
                         fun wp  ->
                           let bs =
                             let uu____2599 = FStar_Syntax_Syntax.mk_binder x
                                in
                             [uu____2599]  in
                           let us =
                             let uu____2621 =
                               let uu____2624 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               [uu____2624]  in
                             u_res :: uu____2621  in
                           let wp1 =
                             FStar_Syntax_Util.abs bs wp
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None
                                     [FStar_Syntax_Syntax.TOTAL]))
                              in
                           let uu____2630 =
                             let uu____2635 =
                               FStar_TypeChecker_Env.inst_effect_fun_with us
                                 env md close1
                                in
                             let uu____2636 =
                               let uu____2637 =
                                 FStar_Syntax_Syntax.as_arg res_t  in
                               let uu____2646 =
                                 let uu____2657 =
                                   FStar_Syntax_Syntax.as_arg
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let uu____2666 =
                                   let uu____2677 =
                                     FStar_Syntax_Syntax.as_arg wp1  in
                                   [uu____2677]  in
                                 uu____2657 :: uu____2666  in
                               uu____2637 :: uu____2646  in
                             FStar_Syntax_Syntax.mk_Tm_app uu____2635
                               uu____2636
                              in
                           uu____2630 FStar_Pervasives_Native.None
                             wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____2719 = destruct_comp c1  in
              match uu____2719 with
              | (u_res_t,res_t,wp) ->
                  let md =
                    FStar_TypeChecker_Env.get_effect_decl env
                      c1.FStar_Syntax_Syntax.effect_name
                     in
                  let wp1 = close_wp u_res_t md res_t bvs wp  in
                  mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1
                    c1.FStar_Syntax_Syntax.flags))
  
let (close_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun bvs  ->
      fun lc  ->
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ
          lc.FStar_TypeChecker_Common.cflags
          (fun uu____2755  ->
             let uu____2756 = FStar_TypeChecker_Common.lcomp_comp lc  in
             close_comp env bvs uu____2756)
  
let (close_comp_if_refinement_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
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
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____2779;
                 FStar_Syntax_Syntax.index = uu____2780;
                 FStar_Syntax_Syntax.sort =
                   { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____2782;
                     FStar_Syntax_Syntax.vars = uu____2783;_};_},uu____2784)
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
              close_comp env [x] c
          | uu____2792 -> c
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_2804  ->
            match uu___0_2804 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____2807 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____2832 =
            let uu____2835 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____2835 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____2832
            (fun c  ->
               (let uu____2891 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____2891) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____2895 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____2895)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____2906 = FStar_Syntax_Util.head_and_args' e  in
                match uu____2906 with
                | (head1,uu____2923) ->
                    let uu____2944 =
                      let uu____2945 = FStar_Syntax_Util.un_uinst head1  in
                      uu____2945.FStar_Syntax_Syntax.n  in
                    (match uu____2944 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2950 =
                           let uu____2952 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____2952
                            in
                         Prims.op_Negation uu____2950
                     | uu____2953 -> true)))
              &&
              (let uu____2956 = should_not_inline_lc lc  in
               Prims.op_Negation uu____2956)
  
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
            let uu____2984 =
              let uu____2986 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____2986  in
            if uu____2984
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____2993 = FStar_Syntax_Util.is_unit t  in
               if uu____2993
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
                    let uu____3002 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____3002
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____3007 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____3007 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____3017 =
                             let uu____3018 =
                               let uu____3023 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____3024 =
                                 let uu____3025 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____3034 =
                                   let uu____3045 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____3045]  in
                                 uu____3025 :: uu____3034  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____3023
                                 uu____3024
                                in
                             uu____3018 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____3017)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____3079 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____3079
           then
             let uu____3084 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____3086 = FStar_Syntax_Print.term_to_string v1  in
             let uu____3088 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____3084 uu____3086 uu____3088
           else ());
          c
  
let (lift_wp_and_bind_with :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.universe ->
          FStar_Syntax_Syntax.typ ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun wp1  ->
      fun md  ->
        fun u_res_t  ->
          fun res_t  ->
            fun wp2  ->
              let r = FStar_TypeChecker_Env.get_range env  in
              let edge =
                let uu____3126 =
                  FStar_TypeChecker_Env.monad_leq env
                    FStar_Parser_Const.effect_PURE_lid
                    md.FStar_Syntax_Syntax.mname
                   in
                match uu____3126 with
                | FStar_Pervasives_Native.Some edge -> edge
                | FStar_Pervasives_Native.None  ->
                    failwith
                      (Prims.op_Hat
                         "Impossible! lift_wp_and_bind_with: did not find a lift from PURE to "
                         (md.FStar_Syntax_Syntax.mname).FStar_Ident.str)
                 in
              let wp11 =
                (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                  FStar_Syntax_Syntax.U_zero FStar_Syntax_Syntax.t_unit wp1
                 in
              let uu____3132 =
                let uu____3137 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [FStar_Syntax_Syntax.U_zero; u_res_t] env md
                    md.FStar_Syntax_Syntax.bind_wp
                   in
                let uu____3138 =
                  let uu____3139 =
                    let uu____3148 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_range r))
                        FStar_Pervasives_Native.None r
                       in
                    FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3148
                     in
                  let uu____3157 =
                    let uu____3168 =
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        FStar_Syntax_Syntax.t_unit
                       in
                    let uu____3185 =
                      let uu____3196 = FStar_Syntax_Syntax.as_arg res_t  in
                      let uu____3205 =
                        let uu____3216 = FStar_Syntax_Syntax.as_arg wp11  in
                        let uu____3225 =
                          let uu____3236 =
                            let uu____3245 =
                              let uu____3246 =
                                let uu____3247 =
                                  FStar_Syntax_Syntax.null_binder
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                [uu____3247]  in
                              FStar_Syntax_Util.abs uu____3246 wp2
                                (FStar_Pervasives_Native.Some
                                   (FStar_Syntax_Util.mk_residual_comp
                                      FStar_Parser_Const.effect_Tot_lid
                                      FStar_Pervasives_Native.None
                                      [FStar_Syntax_Syntax.TOTAL]))
                               in
                            FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                              uu____3245
                             in
                          [uu____3236]  in
                        uu____3216 :: uu____3225  in
                      uu____3196 :: uu____3205  in
                    uu____3168 :: uu____3185  in
                  uu____3139 :: uu____3157  in
                FStar_Syntax_Syntax.mk_Tm_app uu____3137 uu____3138  in
              uu____3132 FStar_Pervasives_Native.None
                wp2.FStar_Syntax_Syntax.pos
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____3336 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_3342  ->
              match uu___1_3342 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____3345 -> false))
       in
    if uu____3336
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_3357  ->
              match uu___2_3357 with
              | FStar_Syntax_Syntax.TOTAL  ->
                  [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | FStar_Syntax_Syntax.RETURN  ->
                  [FStar_Syntax_Syntax.PARTIAL_RETURN;
                  FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | f -> [f]))
  
let (weaken_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      fun formula  ->
        let uu____3377 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____3377
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____3383 = destruct_comp c1  in
           match uu____3383 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let r = FStar_TypeChecker_Env.get_range env  in
               let pure_assume_wp =
                 let uu____3396 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assume_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____3396  in
               let pure_assume_wp1 =
                 let uu____3401 =
                   let uu____3406 =
                     let uu____3407 =
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula
                        in
                     [uu____3407]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____3406
                    in
                 uu____3401 FStar_Pervasives_Native.None r  in
               let w_wp =
                 lift_wp_and_bind_with env pure_assume_wp1 md u_res_t res_t
                   wp
                  in
               let uu____3441 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t w_wp uu____3441)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3465 =
          let c = FStar_TypeChecker_Common.lcomp_comp lc  in
          let uu____3467 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____3467
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____3473 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____3473 weaken
  
let (strengthen_comp :
  FStar_TypeChecker_Env.env ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.formula ->
          FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun reason  ->
      fun c  ->
        fun f  ->
          fun flags  ->
            if env.FStar_TypeChecker_Env.lax
            then c
            else
              (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
               let r = FStar_TypeChecker_Env.get_range env  in
               let uu____3522 = destruct_comp c1  in
               match uu____3522 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let pure_assert_wp =
                     let uu____3534 =
                       FStar_Syntax_Syntax.lid_as_fv
                         FStar_Parser_Const.pure_assert_wp_lid
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____3534  in
                   let pure_assert_wp1 =
                     let uu____3539 =
                       let uu____3544 =
                         let uu____3545 =
                           let uu____3554 = label_opt env reason r f  in
                           FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                             uu____3554
                            in
                         [uu____3545]  in
                       FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp
                         uu____3544
                        in
                     uu____3539 FStar_Pervasives_Native.None r  in
                   let s_wp =
                     lift_wp_and_bind_with env pure_assert_wp1 md u_res_t
                       res_t wp
                      in
                   mk_comp md u_res_t res_t s_wp flags)
  
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
            let uu____3625 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____3625
            then (lc, g0)
            else
              (let flags =
                 let uu____3637 =
                   let uu____3645 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____3645
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____3637 with
                 | (maybe_trivial_post,flags) ->
                     let uu____3675 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_3683  ->
                               match uu___3_3683 with
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
                               | uu____3686 -> []))
                        in
                     FStar_List.append flags uu____3675
                  in
               let strengthen uu____3692 =
                 let c = FStar_TypeChecker_Common.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____3698 = FStar_TypeChecker_Env.guard_form g01  in
                    match uu____3698 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____3701 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____3701
                          then
                            let uu____3705 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debugging_only
                               in
                            let uu____3707 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____3705 uu____3707
                          else ());
                         strengthen_comp env reason c f flags))
                  in
               let uu____3712 =
                 let uu____3713 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____3713
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____3712,
                 (let uu___488_3715 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___488_3715.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___488_3715.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___488_3715.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_3724  ->
            match uu___4_3724 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____3728 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____3757 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____3757
          then e
          else
            (let uu____3764 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____3767 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____3767)
                in
             if uu____3764
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
          fun uu____3820  ->
            match uu____3820 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____3840 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____3840 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____3853 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____3853
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____3863 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____3863
                       then
                         let uu____3868 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____3868
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____3875 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____3875
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____3884 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____3884
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____3891 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____3891
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____3903 =
                  let uu____3904 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____3904
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    lax_mk_tot_or_comp_l joined_eff u_t
                      lc21.FStar_TypeChecker_Common.res_typ []
                  else
                    (let c1 = FStar_TypeChecker_Common.lcomp_comp lc11  in
                     let c2 = FStar_TypeChecker_Common.lcomp_comp lc21  in
                     debug1
                       (fun uu____3921  ->
                          let uu____3922 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____3924 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____3929 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____3922 uu____3924 uu____3929);
                     (let aux uu____3947 =
                        let uu____3948 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____3948
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____3979 ->
                              let uu____3980 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____3980
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____4012 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____4012
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let try_simplify uu____4057 =
                        let uu____4058 =
                          let uu____4060 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____4060  in
                        if uu____4058
                        then
                          let uu____4074 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____4074
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____4097 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____4097))
                        else
                          (let uu____4112 =
                             FStar_Syntax_Util.is_total_comp c1  in
                           if uu____4112
                           then
                             let close1 x reason c =
                               let x1 =
                                 let uu___554_4154 = x  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___554_4154.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___554_4154.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (FStar_Syntax_Util.comp_result c1)
                                 }  in
                               let uu____4155 =
                                 let uu____4161 =
                                   close_comp_if_refinement_t env
                                     x1.FStar_Syntax_Syntax.sort x1 c
                                    in
                                 (uu____4161, reason)  in
                               FStar_Util.Inl uu____4155  in
                             match (e1opt, b) with
                             | (FStar_Pervasives_Native.Some
                                e,FStar_Pervasives_Native.Some x) ->
                                 let uu____4197 =
                                   FStar_All.pipe_right c2
                                     (FStar_Syntax_Subst.subst_comp
                                        [FStar_Syntax_Syntax.NT (x, e)])
                                    in
                                 FStar_All.pipe_right uu____4197
                                   (close1 x "c1 Tot")
                             | (uu____4211,FStar_Pervasives_Native.Some x) ->
                                 FStar_All.pipe_right c2
                                   (close1 x "c1 Tot only close")
                             | (uu____4234,uu____4235) -> aux ()
                           else
                             (let uu____4250 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____4250
                              then
                                let uu____4263 =
                                  let uu____4269 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____4269, "both GTot")  in
                                FStar_Util.Inl uu____4263
                              else aux ()))
                         in
                      let uu____4280 = try_simplify ()  in
                      match uu____4280 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____4306  ->
                                let uu____4307 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____4307);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____4321  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_layered_bind c11 b1 c21 =
                              let uu____4355 =
                                let c1_ed =
                                  FStar_TypeChecker_Env.get_effect_decl env
                                    (FStar_Syntax_Util.comp_effect_name c11)
                                   in
                                let c2_ed =
                                  FStar_TypeChecker_Env.get_effect_decl env
                                    (FStar_Syntax_Util.comp_effect_name c21)
                                   in
                                let uu____4368 =
                                  FStar_TypeChecker_Env.monad_leq env
                                    c1_ed.FStar_Syntax_Syntax.mname
                                    c2_ed.FStar_Syntax_Syntax.mname
                                   in
                                match uu____4368 with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____4381 =
                                      FStar_TypeChecker_Env.monad_leq env
                                        c2_ed.FStar_Syntax_Syntax.mname
                                        c1_ed.FStar_Syntax_Syntax.mname
                                       in
                                    (match uu____4381 with
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           (Prims.op_Hat "Cannot bind "
                                              (Prims.op_Hat
                                                 (c1_ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                 (Prims.op_Hat " and "
                                                    (c2_ed.FStar_Syntax_Syntax.mname).FStar_Ident.str)))
                                     | FStar_Pervasives_Native.Some ed ->
                                         (c21, c2_ed, ed, c11, c1_ed))
                                | FStar_Pervasives_Native.Some ed ->
                                    (c11, c1_ed, ed, c21, c2_ed)
                                 in
                              match uu____4355 with
                              | (c12,uu____4413,uu____4414,c22,c2_ed) ->
                                  let uu____4417 =
                                    lift_to_layered_effect env c12
                                      c2_ed.FStar_Syntax_Syntax.mname
                                     in
                                  (match uu____4417 with
                                   | (c13,g_lift) ->
                                       let uu____4428 =
                                         let uu____4433 =
                                           FStar_Syntax_Util.comp_to_comp_typ
                                             c13
                                            in
                                         let uu____4434 =
                                           FStar_Syntax_Util.comp_to_comp_typ
                                             c22
                                            in
                                         (uu____4433, uu____4434)  in
                                       (match uu____4428 with
                                        | (ct1,ct2) ->
                                            let uu____4441 =
                                              let uu____4452 =
                                                FStar_List.hd
                                                  ct1.FStar_Syntax_Syntax.comp_univs
                                                 in
                                              let uu____4453 =
                                                FStar_List.map
                                                  FStar_Pervasives_Native.fst
                                                  ct1.FStar_Syntax_Syntax.effect_args
                                                 in
                                              (uu____4452,
                                                (ct1.FStar_Syntax_Syntax.result_typ),
                                                uu____4453)
                                               in
                                            (match uu____4441 with
                                             | (u1,t1,is1) ->
                                                 let uu____4487 =
                                                   let uu____4498 =
                                                     FStar_List.hd
                                                       ct2.FStar_Syntax_Syntax.comp_univs
                                                      in
                                                   let uu____4499 =
                                                     FStar_List.map
                                                       FStar_Pervasives_Native.fst
                                                       ct2.FStar_Syntax_Syntax.effect_args
                                                      in
                                                   (uu____4498,
                                                     (ct2.FStar_Syntax_Syntax.result_typ),
                                                     uu____4499)
                                                    in
                                                 (match uu____4487 with
                                                  | (u2,t2,is2) ->
                                                      let uu____4533 =
                                                        FStar_TypeChecker_Env.inst_tscheme_with
                                                          c2_ed.FStar_Syntax_Syntax.bind_wp
                                                          [u1; u2]
                                                         in
                                                      (match uu____4533 with
                                                       | (uu____4542,bind_t)
                                                           ->
                                                           let uu____4544 =
                                                             let uu____4557 =
                                                               let uu____4558
                                                                 =
                                                                 FStar_Syntax_Subst.compress
                                                                   bind_t
                                                                  in
                                                               uu____4558.FStar_Syntax_Syntax.n
                                                                in
                                                             match uu____4557
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs,c) ->
                                                                 let uu____4595
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs c
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____4595
                                                                   (fun
                                                                    uu____4612
                                                                     ->
                                                                    match uu____4612
                                                                    with
                                                                    | 
                                                                    (bs1,c3)
                                                                    ->
                                                                    let uu____4623
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    c3
                                                                    FStar_Syntax_Util.comp_to_comp_typ
                                                                     in
                                                                    (bs1,
                                                                    uu____4623))
                                                             | uu____4624 ->
                                                                 let uu____4625
                                                                   =
                                                                   let uu____4627
                                                                    =
                                                                    let uu____4629
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____4629
                                                                    " is not an arrow"
                                                                     in
                                                                   Prims.op_Hat
                                                                    "bind_t: "
                                                                    uu____4627
                                                                    in
                                                                 failwith
                                                                   uu____4625
                                                              in
                                                           (match uu____4544
                                                            with
                                                            | (bind_bs,bind_ct)
                                                                ->
                                                                let uu____4667
                                                                  =
                                                                  match bind_bs
                                                                  with
                                                                  | a_b::b_b::bs
                                                                    when
                                                                    (FStar_List.length
                                                                    bs) >=
                                                                    (Prims.of_int (2))
                                                                    ->
                                                                    let uu____4794
                                                                    =
                                                                    let uu____4821
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs) -
                                                                    (Prims.of_int (2)))
                                                                    bs  in
                                                                    FStar_All.pipe_right
                                                                    uu____4821
                                                                    (fun
                                                                    uu____4906
                                                                     ->
                                                                    match uu____4906
                                                                    with
                                                                    | 
                                                                    (l1,l2)
                                                                    ->
                                                                    let uu____4987
                                                                    =
                                                                    FStar_List.hd
                                                                    l2  in
                                                                    let uu____5000
                                                                    =
                                                                    let uu____5007
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                    FStar_List.hd
                                                                    uu____5007
                                                                     in
                                                                    (l1,
                                                                    uu____4987,
                                                                    uu____5000))
                                                                     in
                                                                    (match uu____4794
                                                                    with
                                                                    | 
                                                                    (rest_bs,f_b,g_b)
                                                                    ->
                                                                    (a_b,
                                                                    b_b,
                                                                    rest_bs,
                                                                    f_b, g_b))
                                                                  | uu____5165
                                                                    ->
                                                                    let uu____5174
                                                                    =
                                                                    let uu____5176
                                                                    =
                                                                    let uu____5178
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____5178
                                                                    " does not have enough binders"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "bind_t: "
                                                                    uu____5176
                                                                     in
                                                                    failwith
                                                                    uu____5174
                                                                   in
                                                                (match uu____4667
                                                                 with
                                                                 | (a_b,b_b,rest_bs,f_b,g_b)
                                                                    ->
                                                                    let uu____5297
                                                                    =
                                                                    let uu____5304
                                                                    =
                                                                    let uu____5305
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    bind_ct.FStar_Syntax_Syntax.result_typ
                                                                     in
                                                                    uu____5305.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____5304
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____5314,uu____5315::is)
                                                                    ->
                                                                    let uu____5357
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    is  in
                                                                    ((bind_ct.FStar_Syntax_Syntax.comp_univs),
                                                                    uu____5357)
                                                                    | 
                                                                    uu____5374
                                                                    ->
                                                                    let uu____5375
                                                                    =
                                                                    let uu____5377
                                                                    =
                                                                    let uu____5379
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____5379
                                                                    " does not have repr return type"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "bind_t: "
                                                                    uu____5377
                                                                     in
                                                                    failwith
                                                                    uu____5375
                                                                     in
                                                                    (match uu____5297
                                                                    with
                                                                    | 
                                                                    (u_m,is)
                                                                    ->
                                                                    let uu____5399
                                                                    =
                                                                    let uu____5408
                                                                    =
                                                                    let uu____5417
                                                                    =
                                                                    let uu____5426
                                                                    =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env
                                                                    [a_b;
                                                                    b_b]  in
                                                                    (uu____5426,
                                                                    [],
                                                                    FStar_TypeChecker_Env.trivial_guard)
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____5472
                                                                     ->
                                                                    fun b2 
                                                                    ->
                                                                    match uu____5472
                                                                    with
                                                                    | 
                                                                    (env1,is_uvars,g)
                                                                    ->
                                                                    let uu____5503
                                                                    =
                                                                    FStar_TypeChecker_Env.new_implicit_var_aux
                                                                    ""
                                                                    FStar_Range.dummyRange
                                                                    env1
                                                                    (FStar_Pervasives_Native.fst
                                                                    b2).FStar_Syntax_Syntax.sort
                                                                    FStar_Syntax_Syntax.Strict
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (match uu____5503
                                                                    with
                                                                    | 
                                                                    (t,uu____5532,g_t)
                                                                    ->
                                                                    let uu____5546
                                                                    =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env1 
                                                                    [b2]  in
                                                                    let uu____5559
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g g_t  in
                                                                    (uu____5546,
                                                                    (FStar_List.append
                                                                    is_uvars
                                                                    [t]),
                                                                    uu____5559)))
                                                                    uu____5417
                                                                    rest_bs
                                                                     in
                                                                    match uu____5408
                                                                    with
                                                                    | 
                                                                    (uu____5570,rest_bs_uvars,g)
                                                                    ->
                                                                    (rest_bs_uvars,
                                                                    g)  in
                                                                    (match uu____5399
                                                                    with
                                                                    | 
                                                                    (rest_bs_uvars,g_uvars)
                                                                    ->
                                                                    let subst1
                                                                    =
                                                                    FStar_List.map2
                                                                    (fun b2 
                                                                    ->
                                                                    fun t  ->
                                                                    let uu____5619
                                                                    =
                                                                    let uu____5626
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    b2
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    (uu____5626,
                                                                    t)  in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____5619)
                                                                    (a_b ::
                                                                    b_b ::
                                                                    rest_bs)
                                                                    (t1 :: t2
                                                                    ::
                                                                    rest_bs_uvars)
                                                                     in
                                                                    let is3 =
                                                                    FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1)
                                                                    is  in
                                                                    let f_sort_is
                                                                    =
                                                                    let uu____5659
                                                                    =
                                                                    let uu____5660
                                                                    =
                                                                    let uu____5663
                                                                    =
                                                                    let uu____5664
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    f_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    uu____5664.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_Syntax_Subst.compress
                                                                    uu____5663
                                                                     in
                                                                    uu____5660.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____5659
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____5675,uu____5676::is4)
                                                                    ->
                                                                    let uu____5718
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is4
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5718
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1))
                                                                    | 
                                                                    uu____5751
                                                                    ->
                                                                    let uu____5752
                                                                    =
                                                                    let uu____5754
                                                                    =
                                                                    let uu____5756
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____5756
                                                                    " is not a repr type"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "Type of f in bind_t:"
                                                                    uu____5754
                                                                     in
                                                                    failwith
                                                                    uu____5752
                                                                     in
                                                                    let g_sort_is
                                                                    =
                                                                    let x_a =
                                                                    match b1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    t1
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    x ->
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x  in
                                                                    let uu____5779
                                                                    =
                                                                    let uu____5780
                                                                    =
                                                                    let uu____5783
                                                                    =
                                                                    let uu____5784
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    g_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    uu____5784.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_Syntax_Subst.compress
                                                                    uu____5783
                                                                     in
                                                                    uu____5780.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____5779
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____5817
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____5817
                                                                    with
                                                                    | 
                                                                    (bs1,c3)
                                                                    ->
                                                                    let bs_subst
                                                                    =
                                                                    let uu____5827
                                                                    =
                                                                    let uu____5834
                                                                    =
                                                                    let uu____5835
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____5835
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____5856
                                                                    =
                                                                    let uu____5859
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5859
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____5834,
                                                                    uu____5856)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____5827
                                                                     in
                                                                    let c4 =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c3  in
                                                                    let uu____5873
                                                                    =
                                                                    let uu____5874
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c4)  in
                                                                    uu____5874.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5873
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____5879,uu____5880::is4)
                                                                    ->
                                                                    let uu____5922
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is4
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5922
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1))
                                                                    | 
                                                                    uu____5955
                                                                    ->
                                                                    let uu____5956
                                                                    =
                                                                    let uu____5958
                                                                    =
                                                                    let uu____5960
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____5960
                                                                    " is not a repr type"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "Type of g in bind_t:"
                                                                    uu____5958
                                                                     in
                                                                    failwith
                                                                    uu____5956))
                                                                    | 
                                                                    uu____5966
                                                                    ->
                                                                    let uu____5967
                                                                    =
                                                                    let uu____5969
                                                                    =
                                                                    let uu____5971
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____5971
                                                                    " is not a arrow type"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "Type of g in bind_t:"
                                                                    uu____5969
                                                                     in
                                                                    failwith
                                                                    uu____5967
                                                                     in
                                                                    let g =
                                                                    let uu____5978
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_uvars
                                                                    g_lift
                                                                     in
                                                                    FStar_List.fold_left2
                                                                    (fun g 
                                                                    ->
                                                                    fun i1 
                                                                    ->
                                                                    fun f_i1 
                                                                    ->
                                                                    let uu____5986
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env i1
                                                                    f_i1  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____5986)
                                                                    uu____5978
                                                                    is1
                                                                    f_sort_is
                                                                     in
                                                                    let g1 =
                                                                    FStar_List.fold_left2
                                                                    (fun g1 
                                                                    ->
                                                                    fun i1 
                                                                    ->
                                                                    fun g_i1 
                                                                    ->
                                                                    let uu____5995
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env i1
                                                                    g_i1  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g1
                                                                    uu____5995)
                                                                    g is2
                                                                    g_sort_is
                                                                     in
                                                                    let uu____5996
                                                                    =
                                                                    let uu____5997
                                                                    =
                                                                    let uu____5998
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    is3  in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    = u_m;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (c2_ed.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = t2;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____5998;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    uu____5997
                                                                     in
                                                                    (uu____5996,
                                                                    g1))))))))))
                               in
                            let mk_bind c11 b1 c21 =
                              let uu____6037 = lift_and_destruct env c11 c21
                                 in
                              match uu____6037 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____6090 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____6090]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____6110 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____6110]
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
                                    let uu____6157 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____6166 =
                                      let uu____6177 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____6186 =
                                        let uu____6197 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____6206 =
                                          let uu____6217 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____6226 =
                                            let uu____6237 =
                                              let uu____6246 = mk_lam wp2  in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____6246
                                               in
                                            [uu____6237]  in
                                          uu____6217 :: uu____6226  in
                                        uu____6197 :: uu____6206  in
                                      uu____6177 :: uu____6186  in
                                    uu____6157 :: uu____6166  in
                                  let wp =
                                    let uu____6298 =
                                      let uu____6303 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____6303 wp_args
                                       in
                                    uu____6298 FStar_Pervasives_Native.None
                                      t2.FStar_Syntax_Syntax.pos
                                     in
                                  mk_comp md u_t2 t2 wp bind_flags
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
                              let uu____6326 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____6326 with
                              | (m,uu____6334,lift2) ->
                                  let c23 =
                                    let uu____6337 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____6337
                                     in
                                  let uu____6338 = destruct_comp c12  in
                                  (match uu____6338 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____6352 =
                                           let uu____6357 =
                                             let uu____6358 =
                                               FStar_All.pipe_right
                                                 md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                                 FStar_Util.must
                                                in
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               uu____6358
                                              in
                                           let uu____6361 =
                                             let uu____6362 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____6371 =
                                               let uu____6382 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____6382]  in
                                             uu____6362 :: uu____6371  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6357 uu____6361
                                            in
                                         uu____6352
                                           FStar_Pervasives_Native.None r1
                                          in
                                       strengthen_comp env
                                         FStar_Pervasives_Native.None c23 vc1
                                         bind_flags)
                               in
                            let c1_typ =
                              FStar_TypeChecker_Env.unfold_effect_abbrev env
                                c1
                               in
                            let uu____6420 = destruct_comp c1_typ  in
                            match uu____6420 with
                            | (u_res_t1,res_t1,uu____6429) ->
                                let uu____6430 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____6430
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____6435 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____6435
                                   then
                                     (debug1
                                        (fun uu____6445  ->
                                           let uu____6446 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____6448 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____6446 uu____6448);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____6456 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____6459 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____6459)
                                         in
                                      if uu____6456
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
                                                uu____6493 uu____6495);
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
                                                uu____6511 uu____6513);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____6520 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____6520
                                             in
                                          let c22 =
                                            weaken_comp env c21 x_eq_e  in
                                          mk_bind c1 b c22))))
                                else mk_bind c1 b c2))))
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
      | uu____6538 -> g2
  
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
            (let uu____6562 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____6562)
           in
        let flags =
          if should_return1
          then
            let uu____6570 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____6570
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____6586 =
          let c = FStar_TypeChecker_Common.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____6590 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____6590
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____6596 =
              let uu____6598 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____6598  in
            (if uu____6596
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___806_6605 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___806_6605.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___806_6605.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___806_6605.FStar_Syntax_Syntax.effect_args);
                   FStar_Syntax_Syntax.flags = flags
                 }  in
               FStar_Syntax_Syntax.mk_Comp retc2
             else FStar_Syntax_Util.comp_set_flags retc flags)
          else
            (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
             let t = c1.FStar_Syntax_Syntax.result_typ  in
             let c2 = FStar_Syntax_Syntax.mk_Comp c1  in
             let x =
               FStar_Syntax_Syntax.new_bv
                 (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t
                in
             let xexp = FStar_Syntax_Syntax.bv_to_name x  in
             let ret1 =
               let uu____6618 =
                 let uu____6619 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____6619
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                 uu____6618
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____6622 =
               let uu____6623 =
                 let uu____6624 = FStar_TypeChecker_Common.lcomp_of_comp c2
                    in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____6624
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_TypeChecker_Common.lcomp_comp uu____6623  in
             FStar_Syntax_Util.comp_set_flags uu____6622 flags)
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
            fun uu____6662  ->
              match uu____6662 with
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
                    let uu____6674 =
                      ((let uu____6678 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____6678) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____6674
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6696 =
        let uu____6697 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6697  in
      FStar_Syntax_Syntax.fvar uu____6696 FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
  
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
               fun uu____6767  ->
                 match uu____6767 with
                 | (uu____6781,eff_label,uu____6783,uu____6784) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____6797 =
          let uu____6805 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____6843  ->
                    match uu____6843 with
                    | (uu____6858,uu____6859,flags,uu____6861) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_6878  ->
                                match uu___5_6878 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____6881 -> false))))
             in
          if uu____6805
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____6797 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____6914 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____6916 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____6916
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____6957 =
                     FStar_Syntax_Util.get_match_with_close_wps
                       md.FStar_Syntax_Syntax.match_wps
                      in
                   match uu____6957 with
                   | (if_then_else1,uu____6967,uu____6968) ->
                       let uu____6969 =
                         FStar_Range.union_ranges
                           wp_t.FStar_Syntax_Syntax.pos
                           wp_e.FStar_Syntax_Syntax.pos
                          in
                       let uu____6970 =
                         let uu____6975 =
                           FStar_TypeChecker_Env.inst_effect_fun_with
                             [u_res_t] env md if_then_else1
                            in
                         let uu____6976 =
                           let uu____6977 = FStar_Syntax_Syntax.as_arg res_t1
                              in
                           let uu____6986 =
                             let uu____6997 = FStar_Syntax_Syntax.as_arg g
                                in
                             let uu____7006 =
                               let uu____7017 =
                                 FStar_Syntax_Syntax.as_arg wp_t  in
                               let uu____7026 =
                                 let uu____7037 =
                                   FStar_Syntax_Syntax.as_arg wp_e  in
                                 [uu____7037]  in
                               uu____7017 :: uu____7026  in
                             uu____6997 :: uu____7006  in
                           uu____6977 :: uu____6986  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____6975 uu____6976
                          in
                       uu____6970 FStar_Pervasives_Native.None uu____6969
                    in
                 let default_case =
                   let post_k =
                     let uu____7090 =
                       let uu____7099 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____7099]  in
                     let uu____7118 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7090 uu____7118  in
                   let kwp =
                     let uu____7124 =
                       let uu____7133 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____7133]  in
                     let uu____7152 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7124 uu____7152  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____7159 =
                       let uu____7160 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____7160]  in
                     let uu____7179 =
                       let uu____7182 =
                         let uu____7189 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____7189
                          in
                       let uu____7190 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____7182 uu____7190  in
                     FStar_Syntax_Util.abs uu____7159 uu____7179
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
                   let uu____7214 =
                     should_not_inline_whole_match ||
                       (let uu____7217 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____7217)
                      in
                   if uu____7214 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____7256  ->
                        fun celse  ->
                          match uu____7256 with
                          | (g,eff_label,uu____7273,cthen) ->
                              let uu____7287 =
                                let uu____7312 =
                                  let uu____7313 =
                                    maybe_return eff_label cthen  in
                                  FStar_TypeChecker_Common.lcomp_comp
                                    uu____7313
                                   in
                                lift_and_destruct env uu____7312 celse  in
                              (match uu____7287 with
                               | ((md,uu____7315,uu____7316),(uu____7317,uu____7318,wp_then),
                                  (uu____7320,uu____7321,wp_else)) ->
                                   let uu____7341 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____7341 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____7356::[] -> comp
                 | uu____7399 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____7418 = destruct_comp comp1  in
                     (match uu____7418 with
                      | (uu____7425,uu____7426,wp) ->
                          let uu____7428 =
                            FStar_Syntax_Util.get_match_with_close_wps
                              md.FStar_Syntax_Syntax.match_wps
                             in
                          (match uu____7428 with
                           | (uu____7435,ite_wp,uu____7437) ->
                               let wp1 =
                                 let uu____7441 =
                                   let uu____7446 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md ite_wp
                                      in
                                   let uu____7447 =
                                     let uu____7448 =
                                       FStar_Syntax_Syntax.as_arg res_t  in
                                     let uu____7457 =
                                       let uu____7468 =
                                         FStar_Syntax_Syntax.as_arg wp  in
                                       [uu____7468]  in
                                     uu____7448 :: uu____7457  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7446
                                     uu____7447
                                    in
                                 uu____7441 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos
                                  in
                               mk_comp md u_res_t res_t wp1 bind_cases_flags)))
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
          let uu____7534 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____7534 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____7550 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____7556 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____7550 uu____7556
              else
                (let uu____7565 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____7571 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____7565 uu____7571)
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
          let uu____7596 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____7596
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____7599 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____7599
        then u_res
        else
          (let is_total =
             let uu____7606 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____7606
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____7617 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____7617 with
              | FStar_Pervasives_Native.None  ->
                  let uu____7620 =
                    let uu____7626 =
                      let uu____7628 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____7628
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____7626)
                     in
                  FStar_Errors.raise_error uu____7620
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
      let uu____7652 = destruct_comp ct  in
      match uu____7652 with
      | (u_t,t,wp) ->
          let vc =
            let uu____7671 = FStar_TypeChecker_Env.get_range env  in
            let uu____7672 =
              let uu____7677 =
                let uu____7678 =
                  FStar_All.pipe_right md.FStar_Syntax_Syntax.trivial
                    FStar_Util.must
                   in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____7678
                 in
              let uu____7681 =
                let uu____7682 = FStar_Syntax_Syntax.as_arg t  in
                let uu____7691 =
                  let uu____7702 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____7702]  in
                uu____7682 :: uu____7691  in
              FStar_Syntax_Syntax.mk_Tm_app uu____7677 uu____7681  in
            uu____7672 FStar_Pervasives_Native.None uu____7671  in
          let uu____7735 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____7735)
  
let (maybe_coerce_bool_to_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp))
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          if env.FStar_TypeChecker_Env.is_pattern
          then (e, lc)
          else
            (let is_type1 t1 =
               let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
               let uu____7776 =
                 let uu____7777 = FStar_Syntax_Subst.compress t2  in
                 uu____7777.FStar_Syntax_Syntax.n  in
               match uu____7776 with
               | FStar_Syntax_Syntax.Tm_type uu____7781 -> true
               | uu____7783 -> false  in
             let uu____7785 =
               let uu____7786 =
                 FStar_Syntax_Util.unrefine
                   lc.FStar_TypeChecker_Common.res_typ
                  in
               uu____7786.FStar_Syntax_Syntax.n  in
             match uu____7785 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____7794 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____7804 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____7804
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____7807 =
                     let uu____7808 =
                       let uu____7809 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____7809
                        in
                     (FStar_Pervasives_Native.None, uu____7808)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____7807
                    in
                 let e1 =
                   let uu____7815 =
                     let uu____7820 =
                       let uu____7821 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____7821]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____7820  in
                   uu____7815 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____7846 -> (e, lc))
  
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
          (let uu____7881 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____7881
           then
             let uu____7884 = FStar_Syntax_Print.term_to_string e  in
             let uu____7886 = FStar_TypeChecker_Common.lcomp_to_string lc  in
             let uu____7888 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____7884 uu____7886 uu____7888
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____7898 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____7898 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____7923 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____7949 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____7949, false)
             else
               (let uu____7959 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____7959, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____7972) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____7984 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____7984
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___979_8000 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___979_8000.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___979_8000.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___979_8000.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____8007 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____8007 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____8019 =
                      let c = FStar_TypeChecker_Common.lcomp_comp lc  in
                      let res_t = FStar_Syntax_Util.comp_result c  in
                      let set_result_typ1 c1 =
                        FStar_Syntax_Util.set_result_typ c1 t  in
                      let uu____8030 =
                        let uu____8032 = FStar_Syntax_Util.eq_tm t res_t  in
                        uu____8032 = FStar_Syntax_Util.Equal  in
                      if uu____8030
                      then
                        ((let uu____8035 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____8035
                          then
                            let uu____8039 =
                              FStar_Syntax_Print.term_to_string res_t  in
                            let uu____8041 =
                              FStar_Syntax_Print.term_to_string t  in
                            FStar_Util.print2
                              "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                              uu____8039 uu____8041
                          else ());
                         set_result_typ1 c)
                      else
                        (let is_res_t_refinement =
                           let res_t1 =
                             FStar_TypeChecker_Normalize.normalize_refinement
                               FStar_TypeChecker_Normalize.whnf_steps env
                               res_t
                              in
                           match res_t1.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_refine uu____8052 -> true
                           | uu____8060 -> false  in
                         if is_res_t_refinement
                         then
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (res_t.FStar_Syntax_Syntax.pos)) res_t
                              in
                           let cret =
                             let uu____8065 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             return_value env (comp_univ_opt c) res_t
                               uu____8065
                              in
                           let lc1 =
                             let uu____8067 =
                               FStar_TypeChecker_Common.lcomp_of_comp c  in
                             let uu____8068 =
                               let uu____8069 =
                                 FStar_TypeChecker_Common.lcomp_of_comp cret
                                  in
                               ((FStar_Pervasives_Native.Some x), uu____8069)
                                in
                             bind e.FStar_Syntax_Syntax.pos env
                               (FStar_Pervasives_Native.Some e) uu____8067
                               uu____8068
                              in
                           ((let uu____8073 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____8073
                             then
                               let uu____8077 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____8079 =
                                 FStar_Syntax_Print.comp_to_string c  in
                               let uu____8081 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____8083 =
                                 FStar_TypeChecker_Common.lcomp_to_string lc1
                                  in
                               FStar_Util.print4
                                 "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                 uu____8077 uu____8079 uu____8081 uu____8083
                             else ());
                            (let uu____8088 =
                               FStar_TypeChecker_Common.lcomp_comp lc1  in
                             set_result_typ1 uu____8088))
                         else
                           ((let uu____8092 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____8092
                             then
                               let uu____8096 =
                                 FStar_Syntax_Print.term_to_string res_t  in
                               let uu____8098 =
                                 FStar_Syntax_Print.comp_to_string c  in
                               FStar_Util.print2
                                 "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                 uu____8096 uu____8098
                             else ());
                            set_result_typ1 c))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1011_8106 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1011_8106.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1011_8106.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1011_8106.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____8112 =
                      let uu____8113 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____8113
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____8119 =
                           let uu____8120 = FStar_Syntax_Subst.compress f1
                              in
                           uu____8120.FStar_Syntax_Syntax.n  in
                         match uu____8119 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____8123,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____8125;
                                           FStar_Syntax_Syntax.vars =
                                             uu____8126;_},uu____8127)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1027_8153 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1027_8153.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1027_8153.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1027_8153.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____8154 ->
                             let c = FStar_TypeChecker_Common.lcomp_comp lc
                                in
                             ((let uu____8157 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   FStar_Options.Extreme
                                  in
                               if uu____8157
                               then
                                 let uu____8161 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env lc.FStar_TypeChecker_Common.res_typ
                                    in
                                 let uu____8163 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env t
                                    in
                                 let uu____8165 =
                                   FStar_TypeChecker_Normalize.comp_to_string
                                     env c
                                    in
                                 let uu____8167 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env f1
                                    in
                                 FStar_Util.print4
                                   "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                   uu____8161 uu____8163 uu____8165
                                   uu____8167
                               else ());
                              (let u_t_opt = comp_univ_opt c  in
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (t.FStar_Syntax_Syntax.pos)) t
                                  in
                               let xexp = FStar_Syntax_Syntax.bv_to_name x
                                  in
                               let cret = return_value env u_t_opt t xexp  in
                               let guard =
                                 if apply_guard1
                                 then
                                   let uu____8180 =
                                     let uu____8185 =
                                       let uu____8186 =
                                         FStar_Syntax_Syntax.as_arg xexp  in
                                       [uu____8186]  in
                                     FStar_Syntax_Syntax.mk_Tm_app f1
                                       uu____8185
                                      in
                                   uu____8180 FStar_Pervasives_Native.None
                                     f1.FStar_Syntax_Syntax.pos
                                 else f1  in
                               let uu____8213 =
                                 let uu____8218 =
                                   FStar_All.pipe_left
                                     (fun _8239  ->
                                        FStar_Pervasives_Native.Some _8239)
                                     (FStar_TypeChecker_Err.subtyping_failed
                                        env
                                        lc.FStar_TypeChecker_Common.res_typ t)
                                    in
                                 let uu____8240 =
                                   FStar_TypeChecker_Env.set_range env
                                     e.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____8241 =
                                   FStar_TypeChecker_Common.lcomp_of_comp
                                     cret
                                    in
                                 let uu____8242 =
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                     (FStar_TypeChecker_Common.NonTrivial
                                        guard)
                                    in
                                 strengthen_precondition uu____8218
                                   uu____8240 e uu____8241 uu____8242
                                  in
                               match uu____8213 with
                               | (eq_ret,_trivial_so_ok_to_discard) ->
                                   let x1 =
                                     let uu___1043_8246 = x  in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         (uu___1043_8246.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (uu___1043_8246.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (lc.FStar_TypeChecker_Common.res_typ)
                                     }  in
                                   let c1 =
                                     let uu____8248 =
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                         c
                                        in
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (FStar_Pervasives_Native.Some e)
                                       uu____8248
                                       ((FStar_Pervasives_Native.Some x1),
                                         eq_ret)
                                      in
                                   let c2 =
                                     FStar_TypeChecker_Common.lcomp_comp c1
                                      in
                                   ((let uu____8253 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme
                                        in
                                     if uu____8253
                                     then
                                       let uu____8257 =
                                         FStar_TypeChecker_Normalize.comp_to_string
                                           env c2
                                          in
                                       FStar_Util.print1
                                         "Strengthened to %s\n" uu____8257
                                     else ());
                                    c2))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_8270  ->
                              match uu___6_8270 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____8273 -> []))
                       in
                    let lc1 =
                      let uu____8275 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____8275 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1057_8277 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1057_8277.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1057_8277.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1057_8277.FStar_TypeChecker_Common.implicits)
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
        let uu____8313 =
          let uu____8316 =
            let uu____8321 =
              let uu____8322 =
                let uu____8331 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____8331  in
              [uu____8322]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____8321  in
          uu____8316 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____8313  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____8354 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____8354
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____8373 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____8389 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____8406 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____8406
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____8422)::(ens,uu____8424)::uu____8425 ->
                    let uu____8468 =
                      let uu____8471 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____8471  in
                    let uu____8472 =
                      let uu____8473 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____8473  in
                    (uu____8468, uu____8472)
                | uu____8476 ->
                    let uu____8487 =
                      let uu____8493 =
                        let uu____8495 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____8495
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____8493)
                       in
                    FStar_Errors.raise_error uu____8487
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____8515)::uu____8516 ->
                    let uu____8543 =
                      let uu____8548 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____8548
                       in
                    (match uu____8543 with
                     | (us_r,uu____8580) ->
                         let uu____8581 =
                           let uu____8586 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____8586
                            in
                         (match uu____8581 with
                          | (us_e,uu____8618) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____8621 =
                                  let uu____8622 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8622
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8621
                                  us_r
                                 in
                              let as_ens =
                                let uu____8624 =
                                  let uu____8625 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8625
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8624
                                  us_e
                                 in
                              let req =
                                let uu____8629 =
                                  let uu____8634 =
                                    let uu____8635 =
                                      let uu____8646 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8646]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8635
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____8634
                                   in
                                uu____8629 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____8686 =
                                  let uu____8691 =
                                    let uu____8692 =
                                      let uu____8703 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8703]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8692
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____8691
                                   in
                                uu____8686 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____8740 =
                                let uu____8743 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____8743  in
                              let uu____8744 =
                                let uu____8745 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____8745  in
                              (uu____8740, uu____8744)))
                | uu____8748 -> failwith "Impossible"))
  
let (reify_body :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let tm = FStar_Syntax_Util.mk_reify t  in
      let tm' =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Reify;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses] env tm
         in
      (let uu____8782 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____8782
       then
         let uu____8787 = FStar_Syntax_Print.term_to_string tm  in
         let uu____8789 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____8787 uu____8789
       else ());
      tm'
  
let (reify_body_with_arg :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.arg -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun head1  ->
      fun arg  ->
        let tm =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (head1, [arg]))
            FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos
           in
        let tm' =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Eager_unfolding;
            FStar_TypeChecker_Env.EraseUniverses;
            FStar_TypeChecker_Env.AllowUnboundUniverses] env tm
           in
        (let uu____8843 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____8843
         then
           let uu____8848 = FStar_Syntax_Print.term_to_string tm  in
           let uu____8850 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____8848
             uu____8850
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____8861 =
      let uu____8863 =
        let uu____8864 = FStar_Syntax_Subst.compress t  in
        uu____8864.FStar_Syntax_Syntax.n  in
      match uu____8863 with
      | FStar_Syntax_Syntax.Tm_app uu____8868 -> false
      | uu____8886 -> true  in
    if uu____8861
    then t
    else
      (let uu____8891 = FStar_Syntax_Util.head_and_args t  in
       match uu____8891 with
       | (head1,args) ->
           let uu____8934 =
             let uu____8936 =
               let uu____8937 = FStar_Syntax_Subst.compress head1  in
               uu____8937.FStar_Syntax_Syntax.n  in
             match uu____8936 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____8942 -> false  in
           if uu____8934
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____8974 ->
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
          ((let uu____9021 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____9021
            then
              let uu____9024 = FStar_Syntax_Print.term_to_string e  in
              let uu____9026 = FStar_Syntax_Print.term_to_string t  in
              let uu____9028 =
                let uu____9030 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____9030
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____9024 uu____9026 uu____9028
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____9043 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____9043 with
              | (formals,uu____9059) ->
                  let n_implicits =
                    let uu____9081 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____9159  ->
                              match uu____9159 with
                              | (uu____9167,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____9174 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____9174 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____9081 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____9299 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____9299 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____9313 =
                      let uu____9319 =
                        let uu____9321 = FStar_Util.string_of_int n_expected
                           in
                        let uu____9323 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____9325 = FStar_Util.string_of_int n_available
                           in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____9321 uu____9323 uu____9325
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____9319)
                       in
                    let uu____9329 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____9313 uu____9329
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_9347 =
              match uu___7_9347 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____9390 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____9390 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _9521,uu____9508) when
                           _9521 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____9554,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Implicit
                                      uu____9556))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____9590 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____9590 with
                            | (v1,uu____9631,g) ->
                                ((let uu____9646 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____9646
                                  then
                                    let uu____9649 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____9649
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____9659 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____9659 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____9752 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____9752))))
                       | (uu____9779,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____9816 =
                             let uu____9829 =
                               let uu____9836 =
                                 let uu____9841 = FStar_Dyn.mkdyn env  in
                                 (uu____9841, tau)  in
                               FStar_Pervasives_Native.Some uu____9836  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____9829
                              in
                           (match uu____9816 with
                            | (v1,uu____9874,g) ->
                                ((let uu____9889 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____9889
                                  then
                                    let uu____9892 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____9892
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____9902 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____9902 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____9995 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____9995))))
                       | (uu____10022,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____10070 =
                       let uu____10097 = inst_n_binders t1  in
                       aux [] uu____10097 bs1  in
                     (match uu____10070 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____10169) -> (e, torig, guard)
                           | (uu____10200,[]) when
                               let uu____10231 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____10231 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____10233 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____10261 ->
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
            | uu____10274 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____10286 =
      let uu____10290 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____10290
        (FStar_List.map
           (fun u  ->
              let uu____10302 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____10302 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____10286 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____10330 = FStar_Util.set_is_empty x  in
      if uu____10330
      then []
      else
        (let s =
           let uu____10348 =
             let uu____10351 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____10351  in
           FStar_All.pipe_right uu____10348 FStar_Util.set_elements  in
         (let uu____10367 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____10367
          then
            let uu____10372 =
              let uu____10374 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____10374  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____10372
          else ());
         (let r =
            let uu____10383 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____10383  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____10422 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____10422
                     then
                       let uu____10427 =
                         let uu____10429 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____10429
                          in
                       let uu____10433 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____10435 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____10427 uu____10433 uu____10435
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
        let uu____10465 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____10465 FStar_Util.set_elements  in
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
        | ([],uu____10504) -> generalized_univ_names
        | (uu____10511,[]) -> explicit_univ_names
        | uu____10518 ->
            let uu____10527 =
              let uu____10533 =
                let uu____10535 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____10535
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____10533)
               in
            FStar_Errors.raise_error uu____10527 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____10557 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____10557
       then
         let uu____10562 = FStar_Syntax_Print.term_to_string t  in
         let uu____10564 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____10562 uu____10564
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____10573 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____10573
        then
          let uu____10578 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____10578
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____10587 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____10587
         then
           let uu____10592 = FStar_Syntax_Print.term_to_string t  in
           let uu____10594 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____10592 uu____10594
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
        let uu____10678 =
          let uu____10680 =
            FStar_Util.for_all
              (fun uu____10694  ->
                 match uu____10694 with
                 | (uu____10704,uu____10705,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____10680  in
        if uu____10678
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____10757 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____10757
              then
                let uu____10760 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____10760
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____10767 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____10767
               then
                 let uu____10770 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____10770
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____10788 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____10788 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____10822 =
             match uu____10822 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____10859 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____10859
                   then
                     let uu____10864 =
                       let uu____10866 =
                         let uu____10870 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____10870
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____10866
                         (FStar_String.concat ", ")
                        in
                     let uu____10918 =
                       let uu____10920 =
                         let uu____10924 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____10924
                           (FStar_List.map
                              (fun u  ->
                                 let uu____10937 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____10939 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____10937
                                   uu____10939))
                          in
                       FStar_All.pipe_right uu____10920
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____10864
                       uu____10918
                   else ());
                  (let univs2 =
                     let uu____10953 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____10965 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____10965) univs1
                       uu____10953
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____10972 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____10972
                    then
                      let uu____10977 =
                        let uu____10979 =
                          let uu____10983 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____10983
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____10979
                          (FStar_String.concat ", ")
                         in
                      let uu____11031 =
                        let uu____11033 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____11047 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____11049 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____11047
                                    uu____11049))
                           in
                        FStar_All.pipe_right uu____11033
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____10977 uu____11031
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____11070 =
             let uu____11087 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____11087  in
           match uu____11070 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____11177 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____11177
                 then ()
                 else
                   (let uu____11182 = lec_hd  in
                    match uu____11182 with
                    | (lb1,uu____11190,uu____11191) ->
                        let uu____11192 = lec2  in
                        (match uu____11192 with
                         | (lb2,uu____11200,uu____11201) ->
                             let msg =
                               let uu____11204 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____11206 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____11204 uu____11206
                                in
                             let uu____11209 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____11209))
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
                 let uu____11277 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____11277
                 then ()
                 else
                   (let uu____11282 = lec_hd  in
                    match uu____11282 with
                    | (lb1,uu____11290,uu____11291) ->
                        let uu____11292 = lec2  in
                        (match uu____11292 with
                         | (lb2,uu____11300,uu____11301) ->
                             let msg =
                               let uu____11304 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____11306 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____11304 uu____11306
                                in
                             let uu____11309 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____11309))
                  in
               let lecs1 =
                 let uu____11320 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____11373 = univs_and_uvars_of_lec this_lec  in
                        match uu____11373 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____11320 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____11478 = lec_hd  in
                   match uu____11478 with
                   | (lbname,e,c) ->
                       let uu____11488 =
                         let uu____11494 =
                           let uu____11496 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____11498 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____11500 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____11496 uu____11498 uu____11500
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____11494)
                          in
                       let uu____11504 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____11488 uu____11504
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____11523 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____11523 with
                         | FStar_Pervasives_Native.Some uu____11532 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____11540 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____11544 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____11544 with
                              | (bs,kres) ->
                                  ((let uu____11588 =
                                      let uu____11589 =
                                        let uu____11592 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____11592
                                         in
                                      uu____11589.FStar_Syntax_Syntax.n  in
                                    match uu____11588 with
                                    | FStar_Syntax_Syntax.Tm_type uu____11593
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____11597 =
                                          let uu____11599 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____11599  in
                                        if uu____11597
                                        then fail1 kres
                                        else ()
                                    | uu____11604 -> fail1 kres);
                                   (let a =
                                      let uu____11606 =
                                        let uu____11609 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _11612  ->
                                             FStar_Pervasives_Native.Some
                                               _11612) uu____11609
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____11606
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____11620 ->
                                          let uu____11629 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____11629
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
                      (fun uu____11732  ->
                         match uu____11732 with
                         | (lbname,e,c) ->
                             let uu____11778 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____11839 ->
                                   let uu____11852 = (e, c)  in
                                   (match uu____11852 with
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
                                                (fun uu____11892  ->
                                                   match uu____11892 with
                                                   | (x,uu____11898) ->
                                                       let uu____11899 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____11899)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____11917 =
                                                let uu____11919 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____11919
                                                 in
                                              if uu____11917
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
                                          let uu____11928 =
                                            let uu____11929 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____11929.FStar_Syntax_Syntax.n
                                             in
                                          match uu____11928 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____11954 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____11954 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____11965 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____11969 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____11969, gen_tvars))
                                in
                             (match uu____11778 with
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
        (let uu____12116 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____12116
         then
           let uu____12119 =
             let uu____12121 =
               FStar_List.map
                 (fun uu____12136  ->
                    match uu____12136 with
                    | (lb,uu____12145,uu____12146) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____12121 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____12119
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____12172  ->
                match uu____12172 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____12201 = gen env is_rec lecs  in
           match uu____12201 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____12300  ->
                       match uu____12300 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____12362 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____12362
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____12410  ->
                           match uu____12410 with
                           | (l,us,e,c,gvs) ->
                               let uu____12444 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____12446 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____12448 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____12450 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____12452 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____12444 uu____12446 uu____12448
                                 uu____12450 uu____12452))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____12497  ->
                match uu____12497 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____12541 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____12541, t, c, gvs)) univnames_lecs
           generalized_lecs)
  
let (check_and_ascribe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let env1 =
            FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
          let check1 env2 t11 t21 =
            if env2.FStar_TypeChecker_Env.use_eq
            then FStar_TypeChecker_Rel.try_teq true env2 t11 t21
            else
              (let uu____12602 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____12602 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____12608 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _12611  -> FStar_Pervasives_Native.Some _12611)
                     uu____12608)
             in
          let is_var e1 =
            let uu____12619 =
              let uu____12620 = FStar_Syntax_Subst.compress e1  in
              uu____12620.FStar_Syntax_Syntax.n  in
            match uu____12619 with
            | FStar_Syntax_Syntax.Tm_name uu____12624 -> true
            | uu____12626 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1513_12647 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1513_12647.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1513_12647.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____12648 -> e2  in
          let env2 =
            let uu___1516_12650 = env1  in
            let uu____12651 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1516_12650.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1516_12650.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1516_12650.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1516_12650.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1516_12650.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1516_12650.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1516_12650.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1516_12650.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1516_12650.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1516_12650.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1516_12650.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1516_12650.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1516_12650.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1516_12650.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1516_12650.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1516_12650.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1516_12650.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____12651;
              FStar_TypeChecker_Env.is_iface =
                (uu___1516_12650.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1516_12650.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1516_12650.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1516_12650.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1516_12650.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1516_12650.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1516_12650.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1516_12650.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1516_12650.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1516_12650.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1516_12650.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1516_12650.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1516_12650.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1516_12650.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1516_12650.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1516_12650.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1516_12650.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1516_12650.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1516_12650.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1516_12650.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1516_12650.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1516_12650.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1516_12650.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1516_12650.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1516_12650.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1516_12650.FStar_TypeChecker_Env.strict_args_tab)
            }  in
          let uu____12653 = check1 env2 t1 t2  in
          match uu____12653 with
          | FStar_Pervasives_Native.None  ->
              let uu____12660 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____12666 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____12660 uu____12666
          | FStar_Pervasives_Native.Some g ->
              ((let uu____12673 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12673
                then
                  let uu____12678 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____12678
                else ());
               (let uu____12684 = decorate e t2  in (uu____12684, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____12712 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____12712
         then
           let uu____12715 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____12715
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____12729 = FStar_TypeChecker_Common.is_total_lcomp lc  in
         if uu____12729
         then
           let uu____12737 = discharge g1  in
           let uu____12739 = FStar_TypeChecker_Common.lcomp_comp lc  in
           (uu____12737, uu____12739)
         else
           (let c = FStar_TypeChecker_Common.lcomp_comp lc  in
            let steps =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.NoFullNorm;
              FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
            let c1 =
              let uu____12748 =
                let uu____12749 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                FStar_All.pipe_right uu____12749 FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____12748
                (FStar_TypeChecker_Normalize.normalize_comp steps env)
               in
            let uu____12750 = check_trivial_precondition env c1  in
            match uu____12750 with
            | (ct,vc,g2) ->
                ((let uu____12766 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Simplification")
                     in
                  if uu____12766
                  then
                    let uu____12771 = FStar_Syntax_Print.term_to_string vc
                       in
                    FStar_Util.print1 "top-level VC: %s\n" uu____12771
                  else ());
                 (let uu____12776 = discharge g2  in
                  let uu____12778 =
                    FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp  in
                  (uu____12776, uu____12778)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_12812 =
        match uu___8_12812 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____12822)::[] -> f fst1
        | uu____12847 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____12859 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____12859
          (fun _12860  -> FStar_TypeChecker_Common.NonTrivial _12860)
         in
      let op_or_e e =
        let uu____12871 =
          let uu____12872 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____12872  in
        FStar_All.pipe_right uu____12871
          (fun _12875  -> FStar_TypeChecker_Common.NonTrivial _12875)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _12882  -> FStar_TypeChecker_Common.NonTrivial _12882)
         in
      let op_or_t t =
        let uu____12893 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____12893
          (fun _12896  -> FStar_TypeChecker_Common.NonTrivial _12896)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _12903  -> FStar_TypeChecker_Common.NonTrivial _12903)
         in
      let short_op_ite uu___9_12909 =
        match uu___9_12909 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____12919)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____12946)::[] ->
            let uu____12987 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____12987
              (fun _12988  -> FStar_TypeChecker_Common.NonTrivial _12988)
        | uu____12989 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____13001 =
          let uu____13009 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____13009)  in
        let uu____13017 =
          let uu____13027 =
            let uu____13035 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____13035)  in
          let uu____13043 =
            let uu____13053 =
              let uu____13061 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____13061)  in
            let uu____13069 =
              let uu____13079 =
                let uu____13087 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____13087)  in
              let uu____13095 =
                let uu____13105 =
                  let uu____13113 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____13113)  in
                [uu____13105; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____13079 :: uu____13095  in
            uu____13053 :: uu____13069  in
          uu____13027 :: uu____13043  in
        uu____13001 :: uu____13017  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____13175 =
            FStar_Util.find_map table
              (fun uu____13190  ->
                 match uu____13190 with
                 | (x,mk1) ->
                     let uu____13207 = FStar_Ident.lid_equals x lid  in
                     if uu____13207
                     then
                       let uu____13212 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____13212
                     else FStar_Pervasives_Native.None)
             in
          (match uu____13175 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____13216 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____13224 =
      let uu____13225 = FStar_Syntax_Util.un_uinst l  in
      uu____13225.FStar_Syntax_Syntax.n  in
    match uu____13224 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____13230 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____13266)::uu____13267 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____13286 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____13295,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____13296))::uu____13297 -> bs
      | uu____13315 ->
          let uu____13316 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____13316 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____13320 =
                 let uu____13321 = FStar_Syntax_Subst.compress t  in
                 uu____13321.FStar_Syntax_Syntax.n  in
               (match uu____13320 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____13325) ->
                    let uu____13346 =
                      FStar_Util.prefix_until
                        (fun uu___10_13386  ->
                           match uu___10_13386 with
                           | (uu____13394,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____13395)) ->
                               false
                           | uu____13400 -> true) bs'
                       in
                    (match uu____13346 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____13436,uu____13437) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____13509,uu____13510) ->
                         let uu____13583 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____13603  ->
                                   match uu____13603 with
                                   | (x,uu____13612) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____13583
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____13661  ->
                                     match uu____13661 with
                                     | (x,i) ->
                                         let uu____13680 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____13680, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____13691 -> bs))
  
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
            let uu____13720 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____13720
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
          let uu____13751 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____13751
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
        (let uu____13794 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____13794
         then
           ((let uu____13799 = FStar_Ident.text_of_lid lident  in
             d uu____13799);
            (let uu____13801 = FStar_Ident.text_of_lid lident  in
             let uu____13803 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____13801 uu____13803))
         else ());
        (let fv =
           let uu____13809 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____13809
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
         let uu____13821 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1671_13823 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1671_13823.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1671_13823.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1671_13823.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1671_13823.FStar_Syntax_Syntax.sigattrs)
           }), uu____13821))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_13841 =
        match uu___11_13841 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____13844 -> false  in
      let reducibility uu___12_13852 =
        match uu___12_13852 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____13859 -> false  in
      let assumption uu___13_13867 =
        match uu___13_13867 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____13871 -> false  in
      let reification uu___14_13879 =
        match uu___14_13879 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____13882 -> true
        | uu____13884 -> false  in
      let inferred uu___15_13892 =
        match uu___15_13892 with
        | FStar_Syntax_Syntax.Discriminator uu____13894 -> true
        | FStar_Syntax_Syntax.Projector uu____13896 -> true
        | FStar_Syntax_Syntax.RecordType uu____13902 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____13912 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____13925 -> false  in
      let has_eq uu___16_13933 =
        match uu___16_13933 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____13937 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____14016 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____14023 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____14034 =
        let uu____14036 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___17_14042  ->
                  match uu___17_14042 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____14045 -> false))
           in
        FStar_All.pipe_right uu____14036 Prims.op_Negation  in
      if uu____14034
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____14066 =
            let uu____14072 =
              let uu____14074 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____14074 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____14072)  in
          FStar_Errors.raise_error uu____14066 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____14092 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____14100 =
            let uu____14102 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____14102  in
          if uu____14100 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____14112),uu____14113) ->
              ((let uu____14125 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____14125
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____14134 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____14134
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____14145 ->
              let uu____14154 =
                let uu____14156 =
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
                Prims.op_Negation uu____14156  in
              if uu____14154 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____14166 ->
              let uu____14173 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____14173 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____14181 ->
              let uu____14188 =
                let uu____14190 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____14190  in
              if uu____14188 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14200 ->
              let uu____14201 =
                let uu____14203 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____14203  in
              if uu____14201 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14213 ->
              let uu____14214 =
                let uu____14216 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____14216  in
              if uu____14214 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____14226 ->
              let uu____14239 =
                let uu____14241 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____14241  in
              if uu____14239 then err'1 () else ()
          | uu____14251 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let has_erased_for_extraction_attr fv =
        let uu____14274 =
          let uu____14279 =
            FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
          FStar_All.pipe_right uu____14279
            (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
           in
        FStar_All.pipe_right uu____14274
          (fun l_opt  ->
             (FStar_Util.is_some l_opt) &&
               (let uu____14298 = FStar_All.pipe_right l_opt FStar_Util.must
                   in
                FStar_All.pipe_right uu____14298
                  (FStar_List.existsb
                     (fun t1  ->
                        let uu____14316 =
                          let uu____14317 = FStar_Syntax_Subst.compress t1
                             in
                          uu____14317.FStar_Syntax_Syntax.n  in
                        match uu____14316 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            FStar_Ident.lid_equals
                              (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              FStar_Parser_Const.must_erase_for_extraction_attr
                            -> true
                        | uu____14323 -> false))))
         in
      let rec aux_whnf env t1 =
        let uu____14349 =
          let uu____14350 = FStar_Syntax_Subst.compress t1  in
          uu____14350.FStar_Syntax_Syntax.n  in
        match uu____14349 with
        | FStar_Syntax_Syntax.Tm_type uu____14354 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (has_erased_for_extraction_attr fv)
        | FStar_Syntax_Syntax.Tm_arrow uu____14357 ->
            let uu____14372 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____14372 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____14405 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____14405
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____14411;
               FStar_Syntax_Syntax.index = uu____14412;
               FStar_Syntax_Syntax.sort = t2;_},uu____14414)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14423,uu____14424) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____14466::[]) ->
            let uu____14505 =
              let uu____14506 = FStar_Syntax_Util.un_uinst head1  in
              uu____14506.FStar_Syntax_Syntax.n  in
            (match uu____14505 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.erased_lid)
                   || (has_erased_for_extraction_attr fv)
             | uu____14511 -> false)
        | uu____14513 -> false
      
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
            FStar_TypeChecker_Env.Iota] env t1
           in
        let res = aux_whnf env t2  in
        (let uu____14523 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____14523
         then
           let uu____14528 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____14528
         else ());
        res
       in aux g t
  
let (fresh_layered_effect_repr :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.tscheme ->
          FStar_Syntax_Syntax.tscheme ->
            FStar_Syntax_Syntax.universe ->
              FStar_Syntax_Syntax.term ->
                (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun r  ->
      fun eff_name  ->
        fun signature_ts  ->
          fun repr_ts  ->
            fun u  ->
              fun a_tm  ->
                let fail1 t =
                  let uu____14589 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____14589 r  in
                let uu____14599 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____14599 with
                | (uu____14608,signature) ->
                    let uu____14610 =
                      let uu____14611 = FStar_Syntax_Subst.compress signature
                         in
                      uu____14611.FStar_Syntax_Syntax.n  in
                    (match uu____14610 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14619) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____14667 =
                                FStar_List.fold_left
                                  (fun uu____14706  ->
                                     fun uu____14707  ->
                                       match (uu____14706, uu____14707) with
                                       | ((is,g,substs),(b,uu____14754)) ->
                                           let uu____14783 =
                                             let uu____14796 =
                                               FStar_Syntax_Subst.subst
                                                 substs
                                                 b.FStar_Syntax_Syntax.sort
                                                in
                                             new_implicit_var "" r env
                                               uu____14796
                                              in
                                           (match uu____14783 with
                                            | (t,uu____14809,g_t) ->
                                                let uu____14823 =
                                                  FStar_TypeChecker_Env.conj_guard
                                                    g g_t
                                                   in
                                                ((FStar_List.append is [t]),
                                                  uu____14823,
                                                  (FStar_List.append substs
                                                     [FStar_Syntax_Syntax.NT
                                                        (b, t)]))))
                                  ([], FStar_TypeChecker_Env.trivial_guard,
                                    [FStar_Syntax_Syntax.NT
                                       ((FStar_Pervasives_Native.fst a),
                                         a_tm)]) bs2
                                 in
                              (match uu____14667 with
                               | (is,g,uu____14844) ->
                                   let repr =
                                     let uu____14854 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts [u]
                                        in
                                     FStar_All.pipe_right uu____14854
                                       FStar_Pervasives_Native.snd
                                      in
                                   let uu____14863 =
                                     let uu____14864 =
                                       let uu____14869 =
                                         FStar_List.map
                                           FStar_Syntax_Syntax.as_arg (a_tm
                                           :: is)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr
                                         uu____14869
                                        in
                                     uu____14864 FStar_Pervasives_Native.None
                                       r
                                      in
                                   (uu____14863, g))
                          | uu____14878 -> fail1 signature)
                     | uu____14879 -> fail1 signature)
  
let (fresh_layered_effect_repr_en :
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
            let ed = FStar_TypeChecker_Env.get_effect_decl env eff_name  in
            fresh_layered_effect_repr env r eff_name
              ed.FStar_Syntax_Syntax.signature ed.FStar_Syntax_Syntax.repr u
              a_tm
  