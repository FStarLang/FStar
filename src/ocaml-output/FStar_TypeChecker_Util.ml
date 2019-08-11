open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option *
    FStar_Syntax_Syntax.lcomp)
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
            FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t))
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
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
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
             FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred
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
                        FStar_TypeChecker_Env.guard_f =
                          (uu___46_247.FStar_TypeChecker_Env.guard_f);
                        FStar_TypeChecker_Env.deferred = solve_now;
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___46_247.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___46_247.FStar_TypeChecker_Env.implicits)
                      })
                    in
                 let g2 =
                   let uu___49_249 = g1  in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       (uu___49_249.FStar_TypeChecker_Env.guard_f);
                     FStar_TypeChecker_Env.deferred = defer;
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___49_249.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___49_249.FStar_TypeChecker_Env.implicits)
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
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun lc  ->
    let uu____980 = FStar_All.pipe_right lc FStar_Syntax_Syntax.lcomp_comp
       in
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
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____1191 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____1191
        then FStar_Parser_Const.effect_Tot_lid
        else
          join_effects env c1.FStar_Syntax_Syntax.eff_name
            c2.FStar_Syntax_Syntax.eff_name
  
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
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t))
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
  
let (subst_lcomp :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun subst1  ->
    fun lc  ->
      let uu____2380 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____2380
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____2383  ->
           let uu____2384 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____2384)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2392 =
      let uu____2393 = FStar_Syntax_Subst.compress t  in
      uu____2393.FStar_Syntax_Syntax.n  in
    match uu____2392 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2397 -> true
    | uu____2413 -> false
  
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
              let uu____2483 =
                let uu____2485 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____2485  in
              if uu____2483
              then f
              else (let uu____2492 = reason1 ()  in label uu____2492 r f)
  
let (label_guard :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun r  ->
    fun reason  ->
      fun g  ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___314_2513 = g  in
            let uu____2514 =
              let uu____2515 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____2515  in
            {
              FStar_TypeChecker_Env.guard_f = uu____2514;
              FStar_TypeChecker_Env.deferred =
                (uu___314_2513.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___314_2513.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___314_2513.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2536 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____2536
        then c
        else
          (let uu____2541 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____2541
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let uu____2582 =
                  FStar_Syntax_Util.get_match_with_close_wps
                    md.FStar_Syntax_Syntax.match_wps
                   in
                match uu____2582 with
                | (uu____2591,uu____2592,close1) ->
                    FStar_List.fold_right
                      (fun x  ->
                         fun wp  ->
                           let bs =
                             let uu____2615 = FStar_Syntax_Syntax.mk_binder x
                                in
                             [uu____2615]  in
                           let us =
                             let uu____2637 =
                               let uu____2640 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               [uu____2640]  in
                             u_res :: uu____2637  in
                           let wp1 =
                             FStar_Syntax_Util.abs bs wp
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None
                                     [FStar_Syntax_Syntax.TOTAL]))
                              in
                           let uu____2646 =
                             let uu____2651 =
                               FStar_TypeChecker_Env.inst_effect_fun_with us
                                 env md close1
                                in
                             let uu____2652 =
                               let uu____2653 =
                                 FStar_Syntax_Syntax.as_arg res_t  in
                               let uu____2662 =
                                 let uu____2673 =
                                   FStar_Syntax_Syntax.as_arg
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let uu____2682 =
                                   let uu____2693 =
                                     FStar_Syntax_Syntax.as_arg wp1  in
                                   [uu____2693]  in
                                 uu____2673 :: uu____2682  in
                               uu____2653 :: uu____2662  in
                             FStar_Syntax_Syntax.mk_Tm_app uu____2651
                               uu____2652
                              in
                           uu____2646 FStar_Pervasives_Native.None
                             wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____2735 = destruct_comp c1  in
              match uu____2735 with
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
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun bvs  ->
      fun lc  ->
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
          (fun uu____2771  ->
             let uu____2772 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____2772)
  
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
              ({ FStar_Syntax_Syntax.ppname = uu____2795;
                 FStar_Syntax_Syntax.index = uu____2796;
                 FStar_Syntax_Syntax.sort =
                   { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____2798;
                     FStar_Syntax_Syntax.vars = uu____2799;_};_},uu____2800)
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
              close_comp env [x] c
          | uu____2808 -> c
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___0_2820  ->
            match uu___0_2820 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____2823 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____2848 =
            let uu____2851 =
              FStar_All.pipe_right lc.FStar_Syntax_Syntax.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____2851 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____2848
            (fun c  ->
               (let uu____2907 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____2907) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____2911 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____2911)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____2922 = FStar_Syntax_Util.head_and_args' e  in
                match uu____2922 with
                | (head1,uu____2939) ->
                    let uu____2960 =
                      let uu____2961 = FStar_Syntax_Util.un_uinst head1  in
                      uu____2961.FStar_Syntax_Syntax.n  in
                    (match uu____2960 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2966 =
                           let uu____2968 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____2968
                            in
                         Prims.op_Negation uu____2966
                     | uu____2969 -> true)))
              &&
              (let uu____2972 = should_not_inline_lc lc  in
               Prims.op_Negation uu____2972)
  
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
            let uu____3000 =
              let uu____3002 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____3002  in
            if uu____3000
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____3009 = FStar_Syntax_Util.is_unit t  in
               if uu____3009
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
                    let uu____3018 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____3018
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____3023 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____3023 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____3033 =
                             let uu____3034 =
                               let uu____3039 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____3040 =
                                 let uu____3041 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____3050 =
                                   let uu____3061 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____3061]  in
                                 uu____3041 :: uu____3050  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____3039
                                 uu____3040
                                in
                             uu____3034 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____3033)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____3095 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____3095
           then
             let uu____3100 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____3102 = FStar_Syntax_Print.term_to_string v1  in
             let uu____3104 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____3100 uu____3102 uu____3104
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
                let uu____3142 =
                  FStar_TypeChecker_Env.monad_leq env
                    FStar_Parser_Const.effect_PURE_lid
                    md.FStar_Syntax_Syntax.mname
                   in
                match uu____3142 with
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
              let uu____3148 =
                let uu____3153 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [FStar_Syntax_Syntax.U_zero; u_res_t] env md
                    md.FStar_Syntax_Syntax.bind_wp
                   in
                let uu____3154 =
                  let uu____3155 =
                    let uu____3164 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_range r))
                        FStar_Pervasives_Native.None r
                       in
                    FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3164
                     in
                  let uu____3173 =
                    let uu____3184 =
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        FStar_Syntax_Syntax.t_unit
                       in
                    let uu____3201 =
                      let uu____3212 = FStar_Syntax_Syntax.as_arg res_t  in
                      let uu____3221 =
                        let uu____3232 = FStar_Syntax_Syntax.as_arg wp11  in
                        let uu____3241 =
                          let uu____3252 =
                            let uu____3261 =
                              let uu____3262 =
                                let uu____3263 =
                                  FStar_Syntax_Syntax.null_binder
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                [uu____3263]  in
                              FStar_Syntax_Util.abs uu____3262 wp2
                                (FStar_Pervasives_Native.Some
                                   (FStar_Syntax_Util.mk_residual_comp
                                      FStar_Parser_Const.effect_Tot_lid
                                      FStar_Pervasives_Native.None
                                      [FStar_Syntax_Syntax.TOTAL]))
                               in
                            FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                              uu____3261
                             in
                          [uu____3252]  in
                        uu____3232 :: uu____3241  in
                      uu____3212 :: uu____3221  in
                    uu____3184 :: uu____3201  in
                  uu____3155 :: uu____3173  in
                FStar_Syntax_Syntax.mk_Tm_app uu____3153 uu____3154  in
              uu____3148 FStar_Pervasives_Native.None
                wp2.FStar_Syntax_Syntax.pos
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____3352 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_3358  ->
              match uu___1_3358 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____3361 -> false))
       in
    if uu____3352
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_3373  ->
              match uu___2_3373 with
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
        let uu____3393 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____3393
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____3399 = destruct_comp c1  in
           match uu____3399 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let r = FStar_TypeChecker_Env.get_range env  in
               let pure_assume_wp =
                 let uu____3412 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assume_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____3412  in
               let pure_assume_wp1 =
                 let uu____3417 =
                   let uu____3422 =
                     let uu____3423 =
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula
                        in
                     [uu____3423]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____3422
                    in
                 uu____3417 FStar_Pervasives_Native.None r  in
               let w_wp =
                 lift_wp_and_bind_with env pure_assume_wp1 md u_res_t res_t
                   wp
                  in
               let uu____3457 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t w_wp uu____3457)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3481 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____3483 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____3483
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____3489 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____3489 weaken
  
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
               let uu____3538 = destruct_comp c1  in
               match uu____3538 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let pure_assert_wp =
                     let uu____3550 =
                       FStar_Syntax_Syntax.lid_as_fv
                         FStar_Parser_Const.pure_assert_wp_lid
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____3550  in
                   let pure_assert_wp1 =
                     let uu____3555 =
                       let uu____3560 =
                         let uu____3561 =
                           let uu____3570 = label_opt env reason r f  in
                           FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                             uu____3570
                            in
                         [uu____3561]  in
                       FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp
                         uu____3560
                        in
                     uu____3555 FStar_Pervasives_Native.None r  in
                   let s_wp =
                     lift_wp_and_bind_with env pure_assert_wp1 md u_res_t
                       res_t wp
                      in
                   mk_comp md u_res_t res_t s_wp flags)
  
let (strengthen_precondition :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_TypeChecker_Env.guard_t ->
            (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t))
  =
  fun reason  ->
    fun env  ->
      fun e_for_debugging_only  ->
        fun lc  ->
          fun g0  ->
            let uu____3641 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____3641
            then (lc, g0)
            else
              (let flags =
                 let uu____3653 =
                   let uu____3661 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____3661
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____3653 with
                 | (maybe_trivial_post,flags) ->
                     let uu____3691 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___3_3699  ->
                               match uu___3_3699 with
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
                               | uu____3702 -> []))
                        in
                     FStar_List.append flags uu____3691
                  in
               let strengthen uu____3708 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____3714 = FStar_TypeChecker_Env.guard_form g01  in
                    match uu____3714 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____3717 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____3717
                          then
                            let uu____3721 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debugging_only
                               in
                            let uu____3723 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____3721 uu____3723
                          else ());
                         strengthen_comp env reason c f flags))
                  in
               let uu____3728 =
                 let uu____3729 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____3729
                   lc.FStar_Syntax_Syntax.res_typ flags strengthen
                  in
               (uu____3728,
                 (let uu___491_3731 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___491_3731.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___491_3731.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___491_3731.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_3740  ->
            match uu___4_3740 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____3744 -> false) lc.FStar_Syntax_Syntax.cflags)
  
let (maybe_add_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun uopt  ->
      fun lc  ->
        fun e  ->
          let uu____3773 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____3773
          then e
          else
            (let uu____3780 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____3783 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____3783)
                in
             if uu____3780
             then
               let u =
                 match uopt with
                 | FStar_Pervasives_Native.Some u -> u
                 | FStar_Pervasives_Native.None  ->
                     env.FStar_TypeChecker_Env.universe_of env
                       lc.FStar_Syntax_Syntax.res_typ
                  in
               FStar_Syntax_Util.mk_with_type u
                 lc.FStar_Syntax_Syntax.res_typ e
             else e)
  
let (bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.lcomp ->
          lcomp_with_binder -> FStar_Syntax_Syntax.lcomp)
  =
  fun r1  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun uu____3836  ->
            match uu____3836 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____3856 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____3856 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____3869 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____3869
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____3879 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____3879
                       then
                         let uu____3884 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____3884
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____3891 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____3891
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____3900 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____3900
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____3907 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____3907
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____3919 =
                  let uu____3920 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____3920
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_Syntax_Syntax.res_typ
                       in
                    lax_mk_tot_or_comp_l joined_eff u_t
                      lc21.FStar_Syntax_Syntax.res_typ []
                  else
                    (let c1 = FStar_Syntax_Syntax.lcomp_comp lc11  in
                     let c2 = FStar_Syntax_Syntax.lcomp_comp lc21  in
                     debug1
                       (fun uu____3937  ->
                          let uu____3938 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____3940 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____3945 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____3938 uu____3940 uu____3945);
                     (let aux uu____3963 =
                        let uu____3964 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____3964
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____3995 ->
                              let uu____3996 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____3996
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____4028 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____4028
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let try_simplify uu____4073 =
                        let uu____4074 =
                          let uu____4076 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____4076  in
                        if uu____4074
                        then
                          let uu____4090 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____4090
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____4113 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____4113))
                        else
                          (let uu____4128 =
                             FStar_Syntax_Util.is_total_comp c1  in
                           if uu____4128
                           then
                             let close1 x reason c =
                               let x1 =
                                 let uu___557_4170 = x  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___557_4170.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___557_4170.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (FStar_Syntax_Util.comp_result c1)
                                 }  in
                               let uu____4171 =
                                 let uu____4177 =
                                   close_comp_if_refinement_t env
                                     x1.FStar_Syntax_Syntax.sort x1 c
                                    in
                                 (uu____4177, reason)  in
                               FStar_Util.Inl uu____4171  in
                             match (e1opt, b) with
                             | (FStar_Pervasives_Native.Some
                                e,FStar_Pervasives_Native.Some x) ->
                                 let uu____4213 =
                                   FStar_All.pipe_right c2
                                     (FStar_Syntax_Subst.subst_comp
                                        [FStar_Syntax_Syntax.NT (x, e)])
                                    in
                                 FStar_All.pipe_right uu____4213
                                   (close1 x "c1 Tot")
                             | (uu____4227,FStar_Pervasives_Native.Some x) ->
                                 FStar_All.pipe_right c2
                                   (close1 x "c1 Tot only close")
                             | (uu____4250,uu____4251) -> aux ()
                           else
                             (let uu____4266 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____4266
                              then
                                let uu____4279 =
                                  let uu____4285 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____4285, "both GTot")  in
                                FStar_Util.Inl uu____4279
                              else aux ()))
                         in
                      let uu____4296 = try_simplify ()  in
                      match uu____4296 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____4322  ->
                                let uu____4323 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____4323);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____4337  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_layered_bind c11 b1 c21 =
                              let uu____4371 =
                                let c1_ed =
                                  FStar_TypeChecker_Env.get_effect_decl env
                                    (FStar_Syntax_Util.comp_effect_name c11)
                                   in
                                let c2_ed =
                                  FStar_TypeChecker_Env.get_effect_decl env
                                    (FStar_Syntax_Util.comp_effect_name c21)
                                   in
                                let uu____4384 =
                                  FStar_TypeChecker_Env.monad_leq env
                                    c1_ed.FStar_Syntax_Syntax.mname
                                    c2_ed.FStar_Syntax_Syntax.mname
                                   in
                                match uu____4384 with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____4397 =
                                      FStar_TypeChecker_Env.monad_leq env
                                        c2_ed.FStar_Syntax_Syntax.mname
                                        c1_ed.FStar_Syntax_Syntax.mname
                                       in
                                    (match uu____4397 with
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
                              match uu____4371 with
                              | (c12,uu____4429,uu____4430,c22,c2_ed) ->
                                  let uu____4433 =
                                    lift_to_layered_effect env c12
                                      c2_ed.FStar_Syntax_Syntax.mname
                                     in
                                  (match uu____4433 with
                                   | (c13,g_lift) ->
                                       let uu____4444 =
                                         let uu____4449 =
                                           FStar_Syntax_Util.comp_to_comp_typ
                                             c13
                                            in
                                         let uu____4450 =
                                           FStar_Syntax_Util.comp_to_comp_typ
                                             c22
                                            in
                                         (uu____4449, uu____4450)  in
                                       (match uu____4444 with
                                        | (ct1,ct2) ->
                                            let uu____4457 =
                                              let uu____4468 =
                                                FStar_List.hd
                                                  ct1.FStar_Syntax_Syntax.comp_univs
                                                 in
                                              let uu____4469 =
                                                FStar_List.map
                                                  FStar_Pervasives_Native.fst
                                                  ct1.FStar_Syntax_Syntax.effect_args
                                                 in
                                              (uu____4468,
                                                (ct1.FStar_Syntax_Syntax.result_typ),
                                                uu____4469)
                                               in
                                            (match uu____4457 with
                                             | (u1,t1,is1) ->
                                                 let uu____4503 =
                                                   let uu____4514 =
                                                     FStar_List.hd
                                                       ct2.FStar_Syntax_Syntax.comp_univs
                                                      in
                                                   let uu____4515 =
                                                     FStar_List.map
                                                       FStar_Pervasives_Native.fst
                                                       ct2.FStar_Syntax_Syntax.effect_args
                                                      in
                                                   (uu____4514,
                                                     (ct2.FStar_Syntax_Syntax.result_typ),
                                                     uu____4515)
                                                    in
                                                 (match uu____4503 with
                                                  | (u2,t2,is2) ->
                                                      let uu____4549 =
                                                        FStar_TypeChecker_Env.inst_tscheme_with
                                                          c2_ed.FStar_Syntax_Syntax.bind_wp
                                                          [u1; u2]
                                                         in
                                                      (match uu____4549 with
                                                       | (uu____4558,bind_t)
                                                           ->
                                                           let uu____4560 =
                                                             let uu____4573 =
                                                               let uu____4574
                                                                 =
                                                                 FStar_Syntax_Subst.compress
                                                                   bind_t
                                                                  in
                                                               uu____4574.FStar_Syntax_Syntax.n
                                                                in
                                                             match uu____4573
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs,c) ->
                                                                 let uu____4611
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs c
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____4611
                                                                   (fun
                                                                    uu____4628
                                                                     ->
                                                                    match uu____4628
                                                                    with
                                                                    | 
                                                                    (bs1,c3)
                                                                    ->
                                                                    let uu____4639
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    c3
                                                                    FStar_Syntax_Util.comp_to_comp_typ
                                                                     in
                                                                    (bs1,
                                                                    uu____4639))
                                                             | uu____4640 ->
                                                                 let uu____4641
                                                                   =
                                                                   let uu____4643
                                                                    =
                                                                    let uu____4645
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____4645
                                                                    " is not an arrow"
                                                                     in
                                                                   Prims.op_Hat
                                                                    "bind_t: "
                                                                    uu____4643
                                                                    in
                                                                 failwith
                                                                   uu____4641
                                                              in
                                                           (match uu____4560
                                                            with
                                                            | (bind_bs,bind_ct)
                                                                ->
                                                                let uu____4683
                                                                  =
                                                                  match bind_bs
                                                                  with
                                                                  | a_b::b_b::bs
                                                                    when
                                                                    (FStar_List.length
                                                                    bs) >=
                                                                    (Prims.of_int (2))
                                                                    ->
                                                                    let uu____4810
                                                                    =
                                                                    let uu____4837
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs) -
                                                                    (Prims.of_int (2)))
                                                                    bs  in
                                                                    FStar_All.pipe_right
                                                                    uu____4837
                                                                    (fun
                                                                    uu____4922
                                                                     ->
                                                                    match uu____4922
                                                                    with
                                                                    | 
                                                                    (l1,l2)
                                                                    ->
                                                                    let uu____5003
                                                                    =
                                                                    FStar_List.hd
                                                                    l2  in
                                                                    let uu____5016
                                                                    =
                                                                    let uu____5023
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                    FStar_List.hd
                                                                    uu____5023
                                                                     in
                                                                    (l1,
                                                                    uu____5003,
                                                                    uu____5016))
                                                                     in
                                                                    (match uu____4810
                                                                    with
                                                                    | 
                                                                    (rest_bs,f_b,g_b)
                                                                    ->
                                                                    (a_b,
                                                                    b_b,
                                                                    rest_bs,
                                                                    f_b, g_b))
                                                                  | uu____5181
                                                                    ->
                                                                    let uu____5190
                                                                    =
                                                                    let uu____5192
                                                                    =
                                                                    let uu____5194
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____5194
                                                                    " does not have enough binders"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "bind_t: "
                                                                    uu____5192
                                                                     in
                                                                    failwith
                                                                    uu____5190
                                                                   in
                                                                (match uu____4683
                                                                 with
                                                                 | (a_b,b_b,rest_bs,f_b,g_b)
                                                                    ->
                                                                    let uu____5313
                                                                    =
                                                                    let uu____5320
                                                                    =
                                                                    let uu____5321
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    bind_ct.FStar_Syntax_Syntax.result_typ
                                                                     in
                                                                    uu____5321.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____5320
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____5330,uu____5331::is)
                                                                    ->
                                                                    let uu____5373
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    is  in
                                                                    ((bind_ct.FStar_Syntax_Syntax.comp_univs),
                                                                    uu____5373)
                                                                    | 
                                                                    uu____5390
                                                                    ->
                                                                    let uu____5391
                                                                    =
                                                                    let uu____5393
                                                                    =
                                                                    let uu____5395
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____5395
                                                                    " does not have repr return type"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "bind_t: "
                                                                    uu____5393
                                                                     in
                                                                    failwith
                                                                    uu____5391
                                                                     in
                                                                    (match uu____5313
                                                                    with
                                                                    | 
                                                                    (u_m,is)
                                                                    ->
                                                                    let uu____5415
                                                                    =
                                                                    let uu____5424
                                                                    =
                                                                    let uu____5433
                                                                    =
                                                                    let uu____5442
                                                                    =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env
                                                                    [a_b;
                                                                    b_b]  in
                                                                    (uu____5442,
                                                                    [],
                                                                    FStar_TypeChecker_Env.trivial_guard)
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____5488
                                                                     ->
                                                                    fun b2 
                                                                    ->
                                                                    match uu____5488
                                                                    with
                                                                    | 
                                                                    (env1,is_uvars,g)
                                                                    ->
                                                                    let uu____5519
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
                                                                    (match uu____5519
                                                                    with
                                                                    | 
                                                                    (t,uu____5548,g_t)
                                                                    ->
                                                                    let uu____5562
                                                                    =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env1 
                                                                    [b2]  in
                                                                    let uu____5575
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g g_t  in
                                                                    (uu____5562,
                                                                    (FStar_List.append
                                                                    is_uvars
                                                                    [t]),
                                                                    uu____5575)))
                                                                    uu____5433
                                                                    rest_bs
                                                                     in
                                                                    match uu____5424
                                                                    with
                                                                    | 
                                                                    (uu____5586,rest_bs_uvars,g)
                                                                    ->
                                                                    (rest_bs_uvars,
                                                                    g)  in
                                                                    (match uu____5415
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
                                                                    let uu____5635
                                                                    =
                                                                    let uu____5642
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    b2
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    (uu____5642,
                                                                    t)  in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____5635)
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
                                                                    let uu____5675
                                                                    =
                                                                    let uu____5676
                                                                    =
                                                                    let uu____5679
                                                                    =
                                                                    let uu____5680
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    f_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    uu____5680.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_Syntax_Subst.compress
                                                                    uu____5679
                                                                     in
                                                                    uu____5676.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____5675
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____5691,uu____5692::is4)
                                                                    ->
                                                                    let uu____5734
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is4
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5734
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1))
                                                                    | 
                                                                    uu____5767
                                                                    ->
                                                                    let uu____5768
                                                                    =
                                                                    let uu____5770
                                                                    =
                                                                    let uu____5772
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____5772
                                                                    " is not a repr type"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "Type of f in bind_t:"
                                                                    uu____5770
                                                                     in
                                                                    failwith
                                                                    uu____5768
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
                                                                    let uu____5795
                                                                    =
                                                                    let uu____5796
                                                                    =
                                                                    let uu____5799
                                                                    =
                                                                    let uu____5800
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    g_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    uu____5800.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_Syntax_Subst.compress
                                                                    uu____5799
                                                                     in
                                                                    uu____5796.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____5795
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____5833
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____5833
                                                                    with
                                                                    | 
                                                                    (bs1,c3)
                                                                    ->
                                                                    let bs_subst
                                                                    =
                                                                    let uu____5843
                                                                    =
                                                                    let uu____5850
                                                                    =
                                                                    let uu____5851
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____5851
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____5872
                                                                    =
                                                                    let uu____5875
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5875
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____5850,
                                                                    uu____5872)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____5843
                                                                     in
                                                                    let c4 =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c3  in
                                                                    let uu____5889
                                                                    =
                                                                    let uu____5890
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c4)  in
                                                                    uu____5890.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5889
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____5895,uu____5896::is4)
                                                                    ->
                                                                    let uu____5938
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is4
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5938
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1))
                                                                    | 
                                                                    uu____5971
                                                                    ->
                                                                    let uu____5972
                                                                    =
                                                                    let uu____5974
                                                                    =
                                                                    let uu____5976
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____5976
                                                                    " is not a repr type"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "Type of g in bind_t:"
                                                                    uu____5974
                                                                     in
                                                                    failwith
                                                                    uu____5972))
                                                                    | 
                                                                    uu____5982
                                                                    ->
                                                                    let uu____5983
                                                                    =
                                                                    let uu____5985
                                                                    =
                                                                    let uu____5987
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____5987
                                                                    " is not a arrow type"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "Type of g in bind_t:"
                                                                    uu____5985
                                                                     in
                                                                    failwith
                                                                    uu____5983
                                                                     in
                                                                    let g =
                                                                    let uu____5994
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
                                                                    let uu____6002
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env i1
                                                                    f_i1  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____6002)
                                                                    uu____5994
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
                                                                    let uu____6011
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env i1
                                                                    g_i1  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g1
                                                                    uu____6011)
                                                                    g is2
                                                                    g_sort_is
                                                                     in
                                                                    let uu____6012
                                                                    =
                                                                    let uu____6013
                                                                    =
                                                                    let uu____6014
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
                                                                    uu____6014;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    uu____6013
                                                                     in
                                                                    (uu____6012,
                                                                    g1))))))))))
                               in
                            let mk_bind c11 b1 c21 =
                              let uu____6053 = lift_and_destruct env c11 c21
                                 in
                              match uu____6053 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____6106 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____6106]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____6126 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____6126]
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
                                    let uu____6173 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____6182 =
                                      let uu____6193 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____6202 =
                                        let uu____6213 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____6222 =
                                          let uu____6233 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____6242 =
                                            let uu____6253 =
                                              let uu____6262 = mk_lam wp2  in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____6262
                                               in
                                            [uu____6253]  in
                                          uu____6233 :: uu____6242  in
                                        uu____6213 :: uu____6222  in
                                      uu____6193 :: uu____6202  in
                                    uu____6173 :: uu____6182  in
                                  let wp =
                                    let uu____6314 =
                                      let uu____6319 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____6319 wp_args
                                       in
                                    uu____6314 FStar_Pervasives_Native.None
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
                              let uu____6342 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____6342 with
                              | (m,uu____6350,lift2) ->
                                  let c23 =
                                    let uu____6353 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____6353
                                     in
                                  let uu____6354 = destruct_comp c12  in
                                  (match uu____6354 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____6368 =
                                           let uu____6373 =
                                             let uu____6374 =
                                               FStar_All.pipe_right
                                                 md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                                 FStar_Util.must
                                                in
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               uu____6374
                                              in
                                           let uu____6377 =
                                             let uu____6378 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____6387 =
                                               let uu____6398 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____6398]  in
                                             uu____6378 :: uu____6387  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6373 uu____6377
                                            in
                                         uu____6368
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
                            let uu____6436 = destruct_comp c1_typ  in
                            match uu____6436 with
                            | (u_res_t1,res_t1,uu____6445) ->
                                let uu____6446 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____6446
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____6451 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____6451
                                   then
                                     (debug1
                                        (fun uu____6461  ->
                                           let uu____6462 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____6464 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____6462 uu____6464);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____6472 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____6475 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____6475)
                                         in
                                      if uu____6472
                                      then
                                        let e1' =
                                          let uu____6496 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____6496
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____6508  ->
                                              let uu____6509 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____6511 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____6509 uu____6511);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____6526  ->
                                              let uu____6527 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____6529 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____6527 uu____6529);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____6536 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____6536
                                             in
                                          let c22 =
                                            weaken_comp env c21 x_eq_e  in
                                          mk_bind c1 b c22))))
                                else mk_bind c1 b c2))))
                   in
                FStar_Syntax_Syntax.mk_lcomp joined_eff
                  lc21.FStar_Syntax_Syntax.res_typ bind_flags bind_it
  
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
      | uu____6554 -> g2
  
let (maybe_assume_result_eq_pure_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
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
            (let uu____6578 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____6578)
           in
        let flags =
          if should_return1
          then
            let uu____6586 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____6586
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____6602 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____6606 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____6606
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____6612 =
              let uu____6614 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____6614  in
            (if uu____6612
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___809_6621 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___809_6621.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___809_6621.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___809_6621.FStar_Syntax_Syntax.effect_args);
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
               let uu____6634 =
                 let uu____6635 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____6635
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6634
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____6638 =
               let uu____6639 =
                 let uu____6640 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____6640
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____6639  in
             FStar_Syntax_Util.comp_set_flags uu____6638 flags)
           in
        if Prims.op_Negation should_return1
        then lc
        else
          FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
            lc.FStar_Syntax_Syntax.res_typ flags refine1
  
let (maybe_return_e2_and_bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_Syntax_Syntax.term ->
            lcomp_with_binder -> FStar_Syntax_Syntax.lcomp)
  =
  fun r  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun e2  ->
            fun uu____6678  ->
              match uu____6678 with
              | (x,lc2) ->
                  let lc21 =
                    let eff1 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc1.FStar_Syntax_Syntax.eff_name
                       in
                    let eff2 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc2.FStar_Syntax_Syntax.eff_name
                       in
                    let uu____6690 =
                      ((let uu____6694 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____6694) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____6690
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6712 =
        let uu____6713 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6713  in
      FStar_Syntax_Syntax.fvar uu____6712 FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
  
let (bind_cases :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ * FStar_Ident.lident *
        FStar_Syntax_Syntax.cflag Prims.list *
        (Prims.bool -> FStar_Syntax_Syntax.lcomp)) Prims.list ->
        FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun res_t  ->
      fun lcases  ->
        let eff =
          FStar_List.fold_left
            (fun eff  ->
               fun uu____6783  ->
                 match uu____6783 with
                 | (uu____6797,eff_label,uu____6799,uu____6800) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____6813 =
          let uu____6821 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____6859  ->
                    match uu____6859 with
                    | (uu____6874,uu____6875,flags,uu____6877) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_6894  ->
                                match uu___5_6894 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____6897 -> false))))
             in
          if uu____6821
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____6813 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____6930 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____6932 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____6932
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____6973 =
                     FStar_Syntax_Util.get_match_with_close_wps
                       md.FStar_Syntax_Syntax.match_wps
                      in
                   match uu____6973 with
                   | (if_then_else1,uu____6983,uu____6984) ->
                       let uu____6985 =
                         FStar_Range.union_ranges
                           wp_t.FStar_Syntax_Syntax.pos
                           wp_e.FStar_Syntax_Syntax.pos
                          in
                       let uu____6986 =
                         let uu____6991 =
                           FStar_TypeChecker_Env.inst_effect_fun_with
                             [u_res_t] env md if_then_else1
                            in
                         let uu____6992 =
                           let uu____6993 = FStar_Syntax_Syntax.as_arg res_t1
                              in
                           let uu____7002 =
                             let uu____7013 = FStar_Syntax_Syntax.as_arg g
                                in
                             let uu____7022 =
                               let uu____7033 =
                                 FStar_Syntax_Syntax.as_arg wp_t  in
                               let uu____7042 =
                                 let uu____7053 =
                                   FStar_Syntax_Syntax.as_arg wp_e  in
                                 [uu____7053]  in
                               uu____7033 :: uu____7042  in
                             uu____7013 :: uu____7022  in
                           uu____6993 :: uu____7002  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____6991 uu____6992
                          in
                       uu____6986 FStar_Pervasives_Native.None uu____6985
                    in
                 let default_case =
                   let post_k =
                     let uu____7106 =
                       let uu____7115 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____7115]  in
                     let uu____7134 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7106 uu____7134  in
                   let kwp =
                     let uu____7140 =
                       let uu____7149 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____7149]  in
                     let uu____7168 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7140 uu____7168  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____7175 =
                       let uu____7176 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____7176]  in
                     let uu____7195 =
                       let uu____7198 =
                         let uu____7205 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____7205
                          in
                       let uu____7206 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____7198 uu____7206  in
                     FStar_Syntax_Util.abs uu____7175 uu____7195
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
                   let uu____7230 =
                     should_not_inline_whole_match ||
                       (let uu____7233 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____7233)
                      in
                   if uu____7230 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____7272  ->
                        fun celse  ->
                          match uu____7272 with
                          | (g,eff_label,uu____7289,cthen) ->
                              let uu____7303 =
                                let uu____7328 =
                                  let uu____7329 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____7329
                                   in
                                lift_and_destruct env uu____7328 celse  in
                              (match uu____7303 with
                               | ((md,uu____7331,uu____7332),(uu____7333,uu____7334,wp_then),
                                  (uu____7336,uu____7337,wp_else)) ->
                                   let uu____7357 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____7357 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____7372::[] -> comp
                 | uu____7415 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____7434 = destruct_comp comp1  in
                     (match uu____7434 with
                      | (uu____7441,uu____7442,wp) ->
                          let uu____7444 =
                            FStar_Syntax_Util.get_match_with_close_wps
                              md.FStar_Syntax_Syntax.match_wps
                             in
                          (match uu____7444 with
                           | (uu____7451,ite_wp,uu____7453) ->
                               let wp1 =
                                 let uu____7457 =
                                   let uu____7462 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md ite_wp
                                      in
                                   let uu____7463 =
                                     let uu____7464 =
                                       FStar_Syntax_Syntax.as_arg res_t  in
                                     let uu____7473 =
                                       let uu____7484 =
                                         FStar_Syntax_Syntax.as_arg wp  in
                                       [uu____7484]  in
                                     uu____7464 :: uu____7473  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7462
                                     uu____7463
                                    in
                                 uu____7457 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos
                                  in
                               mk_comp md u_res_t res_t wp1 bind_cases_flags)))
               in
            FStar_Syntax_Syntax.mk_lcomp eff res_t bind_cases_flags
              bind_cases
  
let (check_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
            FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____7550 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____7550 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____7566 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____7572 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____7566 uu____7572
              else
                (let uu____7581 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____7587 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____7581 uu____7587)
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
          let uu____7612 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____7612
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____7615 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____7615
        then u_res
        else
          (let is_total =
             let uu____7622 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____7622
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____7633 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____7633 with
              | FStar_Pervasives_Native.None  ->
                  let uu____7636 =
                    let uu____7642 =
                      let uu____7644 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____7644
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____7642)
                     in
                  FStar_Errors.raise_error uu____7636
                    c.FStar_Syntax_Syntax.pos
              | FStar_Pervasives_Native.Some tm ->
                  env.FStar_TypeChecker_Env.universe_of env tm))
  
let (check_trivial_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp_typ * FStar_Syntax_Syntax.formula *
        FStar_TypeChecker_Env.guard_t))
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
      let uu____7668 = destruct_comp ct  in
      match uu____7668 with
      | (u_t,t,wp) ->
          let vc =
            let uu____7687 = FStar_TypeChecker_Env.get_range env  in
            let uu____7688 =
              let uu____7693 =
                let uu____7694 =
                  FStar_All.pipe_right md.FStar_Syntax_Syntax.trivial
                    FStar_Util.must
                   in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____7694
                 in
              let uu____7697 =
                let uu____7698 = FStar_Syntax_Syntax.as_arg t  in
                let uu____7707 =
                  let uu____7718 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____7718]  in
                uu____7698 :: uu____7707  in
              FStar_Syntax_Syntax.mk_Tm_app uu____7693 uu____7697  in
            uu____7688 FStar_Pervasives_Native.None uu____7687  in
          let uu____7751 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____7751)
  
let (maybe_coerce_bool_to_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp))
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
               let uu____7792 =
                 let uu____7793 = FStar_Syntax_Subst.compress t2  in
                 uu____7793.FStar_Syntax_Syntax.n  in
               match uu____7792 with
               | FStar_Syntax_Syntax.Tm_type uu____7797 -> true
               | uu____7799 -> false  in
             let uu____7801 =
               let uu____7802 =
                 FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ
                  in
               uu____7802.FStar_Syntax_Syntax.n  in
             match uu____7801 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____7810 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____7820 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____7820
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____7823 =
                     let uu____7824 =
                       let uu____7825 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____7825
                        in
                     (FStar_Pervasives_Native.None, uu____7824)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____7823
                    in
                 let e1 =
                   let uu____7831 =
                     let uu____7836 =
                       let uu____7837 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____7837]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____7836  in
                   uu____7831 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____7862 -> (e, lc))
  
let (weaken_result_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
            FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          (let uu____7897 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____7897
           then
             let uu____7900 = FStar_Syntax_Print.term_to_string e  in
             let uu____7902 = FStar_Syntax_Print.lcomp_to_string lc  in
             let uu____7904 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____7900 uu____7902 uu____7904
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____7914 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_Syntax_Syntax.eff_name
                   in
                match uu____7914 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____7939 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____7965 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____7965, false)
             else
               (let uu____7975 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_Syntax_Syntax.res_typ t
                   in
                (uu____7975, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____7988) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____8000 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_Syntax_Syntax.res_typ
                    in
                 FStar_Errors.raise_error uu____8000
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_Syntax_Syntax.res_typ t;
                  (e,
                    ((let uu___982_8016 = lc  in
                      {
                        FStar_Syntax_Syntax.eff_name =
                          (uu___982_8016.FStar_Syntax_Syntax.eff_name);
                        FStar_Syntax_Syntax.res_typ = t;
                        FStar_Syntax_Syntax.cflags =
                          (uu___982_8016.FStar_Syntax_Syntax.cflags);
                        FStar_Syntax_Syntax.comp_thunk =
                          (uu___982_8016.FStar_Syntax_Syntax.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____8023 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____8023 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____8035 =
                      let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                      let res_t = FStar_Syntax_Util.comp_result c  in
                      let set_result_typ1 c1 =
                        FStar_Syntax_Util.set_result_typ c1 t  in
                      let uu____8046 =
                        let uu____8048 = FStar_Syntax_Util.eq_tm t res_t  in
                        uu____8048 = FStar_Syntax_Util.Equal  in
                      if uu____8046
                      then
                        ((let uu____8051 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____8051
                          then
                            let uu____8055 =
                              FStar_Syntax_Print.term_to_string res_t  in
                            let uu____8057 =
                              FStar_Syntax_Print.term_to_string t  in
                            FStar_Util.print2
                              "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                              uu____8055 uu____8057
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
                           | FStar_Syntax_Syntax.Tm_refine uu____8068 -> true
                           | uu____8076 -> false  in
                         if is_res_t_refinement
                         then
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (res_t.FStar_Syntax_Syntax.pos)) res_t
                              in
                           let cret =
                             let uu____8081 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             return_value env (comp_univ_opt c) res_t
                               uu____8081
                              in
                           let lc1 =
                             let uu____8083 =
                               FStar_Syntax_Util.lcomp_of_comp c  in
                             let uu____8084 =
                               let uu____8085 =
                                 FStar_Syntax_Util.lcomp_of_comp cret  in
                               ((FStar_Pervasives_Native.Some x), uu____8085)
                                in
                             bind e.FStar_Syntax_Syntax.pos env
                               (FStar_Pervasives_Native.Some e) uu____8083
                               uu____8084
                              in
                           ((let uu____8089 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____8089
                             then
                               let uu____8093 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____8095 =
                                 FStar_Syntax_Print.comp_to_string c  in
                               let uu____8097 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____8099 =
                                 FStar_Syntax_Print.lcomp_to_string lc1  in
                               FStar_Util.print4
                                 "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                 uu____8093 uu____8095 uu____8097 uu____8099
                             else ());
                            (let uu____8104 =
                               FStar_Syntax_Syntax.lcomp_comp lc1  in
                             set_result_typ1 uu____8104))
                         else
                           ((let uu____8108 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____8108
                             then
                               let uu____8112 =
                                 FStar_Syntax_Print.term_to_string res_t  in
                               let uu____8114 =
                                 FStar_Syntax_Print.comp_to_string c  in
                               FStar_Util.print2
                                 "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                 uu____8112 uu____8114
                             else ());
                            set_result_typ1 c))
                       in
                    let lc1 =
                      FStar_Syntax_Syntax.mk_lcomp
                        lc.FStar_Syntax_Syntax.eff_name t
                        lc.FStar_Syntax_Syntax.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1014_8122 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___1014_8122.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___1014_8122.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___1014_8122.FStar_TypeChecker_Env.implicits)
                      }  in
                    let strengthen uu____8128 =
                      let uu____8129 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____8129
                      then FStar_Syntax_Syntax.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____8135 =
                           let uu____8136 = FStar_Syntax_Subst.compress f1
                              in
                           uu____8136.FStar_Syntax_Syntax.n  in
                         match uu____8135 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____8139,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____8141;
                                           FStar_Syntax_Syntax.vars =
                                             uu____8142;_},uu____8143)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1030_8169 = lc  in
                               {
                                 FStar_Syntax_Syntax.eff_name =
                                   (uu___1030_8169.FStar_Syntax_Syntax.eff_name);
                                 FStar_Syntax_Syntax.res_typ = t;
                                 FStar_Syntax_Syntax.cflags =
                                   (uu___1030_8169.FStar_Syntax_Syntax.cflags);
                                 FStar_Syntax_Syntax.comp_thunk =
                                   (uu___1030_8169.FStar_Syntax_Syntax.comp_thunk)
                               }  in
                             FStar_Syntax_Syntax.lcomp_comp lc1
                         | uu____8170 ->
                             let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                             ((let uu____8173 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   FStar_Options.Extreme
                                  in
                               if uu____8173
                               then
                                 let uu____8177 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env lc.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8179 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env t
                                    in
                                 let uu____8181 =
                                   FStar_TypeChecker_Normalize.comp_to_string
                                     env c
                                    in
                                 let uu____8183 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env f1
                                    in
                                 FStar_Util.print4
                                   "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                   uu____8177 uu____8179 uu____8181
                                   uu____8183
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
                                   let uu____8196 =
                                     let uu____8201 =
                                       let uu____8202 =
                                         FStar_Syntax_Syntax.as_arg xexp  in
                                       [uu____8202]  in
                                     FStar_Syntax_Syntax.mk_Tm_app f1
                                       uu____8201
                                      in
                                   uu____8196 FStar_Pervasives_Native.None
                                     f1.FStar_Syntax_Syntax.pos
                                 else f1  in
                               let uu____8229 =
                                 let uu____8234 =
                                   FStar_All.pipe_left
                                     (fun _8255  ->
                                        FStar_Pervasives_Native.Some _8255)
                                     (FStar_TypeChecker_Err.subtyping_failed
                                        env lc.FStar_Syntax_Syntax.res_typ t)
                                    in
                                 let uu____8256 =
                                   FStar_TypeChecker_Env.set_range env
                                     e.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____8257 =
                                   FStar_Syntax_Util.lcomp_of_comp cret  in
                                 let uu____8258 =
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                     (FStar_TypeChecker_Common.NonTrivial
                                        guard)
                                    in
                                 strengthen_precondition uu____8234
                                   uu____8256 e uu____8257 uu____8258
                                  in
                               match uu____8229 with
                               | (eq_ret,_trivial_so_ok_to_discard) ->
                                   let x1 =
                                     let uu___1046_8262 = x  in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         (uu___1046_8262.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (uu___1046_8262.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (lc.FStar_Syntax_Syntax.res_typ)
                                     }  in
                                   let c1 =
                                     let uu____8264 =
                                       FStar_Syntax_Util.lcomp_of_comp c  in
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (FStar_Pervasives_Native.Some e)
                                       uu____8264
                                       ((FStar_Pervasives_Native.Some x1),
                                         eq_ret)
                                      in
                                   let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                      in
                                   ((let uu____8269 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme
                                        in
                                     if uu____8269
                                     then
                                       let uu____8273 =
                                         FStar_TypeChecker_Normalize.comp_to_string
                                           env c2
                                          in
                                       FStar_Util.print1
                                         "Strengthened to %s\n" uu____8273
                                     else ());
                                    c2))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                        (FStar_List.collect
                           (fun uu___6_8286  ->
                              match uu___6_8286 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____8289 -> []))
                       in
                    let lc1 =
                      let uu____8291 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_Syntax_Syntax.eff_name
                         in
                      FStar_Syntax_Syntax.mk_lcomp uu____8291 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1060_8293 = g1  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___1060_8293.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___1060_8293.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___1060_8293.FStar_TypeChecker_Env.implicits)
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
        let uu____8329 =
          let uu____8332 =
            let uu____8337 =
              let uu____8338 =
                let uu____8347 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____8347  in
              [uu____8338]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____8337  in
          uu____8332 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____8329  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____8370 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____8370
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____8389 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____8405 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____8422 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____8422
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____8438)::(ens,uu____8440)::uu____8441 ->
                    let uu____8484 =
                      let uu____8487 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____8487  in
                    let uu____8488 =
                      let uu____8489 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____8489  in
                    (uu____8484, uu____8488)
                | uu____8492 ->
                    let uu____8503 =
                      let uu____8509 =
                        let uu____8511 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____8511
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____8509)
                       in
                    FStar_Errors.raise_error uu____8503
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____8531)::uu____8532 ->
                    let uu____8559 =
                      let uu____8564 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____8564
                       in
                    (match uu____8559 with
                     | (us_r,uu____8596) ->
                         let uu____8597 =
                           let uu____8602 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____8602
                            in
                         (match uu____8597 with
                          | (us_e,uu____8634) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____8637 =
                                  let uu____8638 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8638
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8637
                                  us_r
                                 in
                              let as_ens =
                                let uu____8640 =
                                  let uu____8641 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8641
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8640
                                  us_e
                                 in
                              let req =
                                let uu____8645 =
                                  let uu____8650 =
                                    let uu____8651 =
                                      let uu____8662 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8662]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8651
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____8650
                                   in
                                uu____8645 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____8702 =
                                  let uu____8707 =
                                    let uu____8708 =
                                      let uu____8719 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8719]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8708
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____8707
                                   in
                                uu____8702 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____8756 =
                                let uu____8759 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____8759  in
                              let uu____8760 =
                                let uu____8761 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____8761  in
                              (uu____8756, uu____8760)))
                | uu____8764 -> failwith "Impossible"))
  
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
      (let uu____8798 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____8798
       then
         let uu____8803 = FStar_Syntax_Print.term_to_string tm  in
         let uu____8805 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____8803 uu____8805
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
        (let uu____8859 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____8859
         then
           let uu____8864 = FStar_Syntax_Print.term_to_string tm  in
           let uu____8866 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____8864
             uu____8866
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____8877 =
      let uu____8879 =
        let uu____8880 = FStar_Syntax_Subst.compress t  in
        uu____8880.FStar_Syntax_Syntax.n  in
      match uu____8879 with
      | FStar_Syntax_Syntax.Tm_app uu____8884 -> false
      | uu____8902 -> true  in
    if uu____8877
    then t
    else
      (let uu____8907 = FStar_Syntax_Util.head_and_args t  in
       match uu____8907 with
       | (head1,args) ->
           let uu____8950 =
             let uu____8952 =
               let uu____8953 = FStar_Syntax_Subst.compress head1  in
               uu____8953.FStar_Syntax_Syntax.n  in
             match uu____8952 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____8958 -> false  in
           if uu____8950
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____8990 ->
                  failwith
                    "Impossible : Reify applied to multiple arguments after normalization.")
           else t)
  
let (maybe_instantiate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
          FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let torig = FStar_Syntax_Subst.compress t  in
        if Prims.op_Negation env.FStar_TypeChecker_Env.instantiate_imp
        then (e, torig, FStar_TypeChecker_Env.trivial_guard)
        else
          ((let uu____9037 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____9037
            then
              let uu____9040 = FStar_Syntax_Print.term_to_string e  in
              let uu____9042 = FStar_Syntax_Print.term_to_string t  in
              let uu____9044 =
                let uu____9046 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____9046
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____9040 uu____9042 uu____9044
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____9059 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____9059 with
              | (formals,uu____9075) ->
                  let n_implicits =
                    let uu____9097 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____9175  ->
                              match uu____9175 with
                              | (uu____9183,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____9190 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____9190 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____9097 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____9315 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____9315 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____9329 =
                      let uu____9335 =
                        let uu____9337 = FStar_Util.string_of_int n_expected
                           in
                        let uu____9339 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____9341 = FStar_Util.string_of_int n_available
                           in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____9337 uu____9339 uu____9341
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____9335)
                       in
                    let uu____9345 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____9329 uu____9345
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_9363 =
              match uu___7_9363 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____9406 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____9406 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _9537,uu____9524) when
                           _9537 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____9570,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Implicit
                                      uu____9572))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____9606 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____9606 with
                            | (v1,uu____9647,g) ->
                                ((let uu____9662 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____9662
                                  then
                                    let uu____9665 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____9665
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____9675 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____9675 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____9768 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____9768))))
                       | (uu____9795,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____9832 =
                             let uu____9845 =
                               let uu____9852 =
                                 let uu____9857 = FStar_Dyn.mkdyn env  in
                                 (uu____9857, tau)  in
                               FStar_Pervasives_Native.Some uu____9852  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____9845
                              in
                           (match uu____9832 with
                            | (v1,uu____9890,g) ->
                                ((let uu____9905 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____9905
                                  then
                                    let uu____9908 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____9908
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____9918 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____9918 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____10011 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____10011))))
                       | (uu____10038,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____10086 =
                       let uu____10113 = inst_n_binders t1  in
                       aux [] uu____10113 bs1  in
                     (match uu____10086 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____10185) -> (e, torig, guard)
                           | (uu____10216,[]) when
                               let uu____10247 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____10247 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____10249 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____10277 ->
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
            | uu____10290 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____10302 =
      let uu____10306 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____10306
        (FStar_List.map
           (fun u  ->
              let uu____10318 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____10318 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____10302 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____10346 = FStar_Util.set_is_empty x  in
      if uu____10346
      then []
      else
        (let s =
           let uu____10364 =
             let uu____10367 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____10367  in
           FStar_All.pipe_right uu____10364 FStar_Util.set_elements  in
         (let uu____10383 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____10383
          then
            let uu____10388 =
              let uu____10390 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____10390  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____10388
          else ());
         (let r =
            let uu____10399 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____10399  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____10438 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____10438
                     then
                       let uu____10443 =
                         let uu____10445 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____10445
                          in
                       let uu____10449 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____10451 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____10443 uu____10449 uu____10451
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
        let uu____10481 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____10481 FStar_Util.set_elements  in
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
        | ([],uu____10520) -> generalized_univ_names
        | (uu____10527,[]) -> explicit_univ_names
        | uu____10534 ->
            let uu____10543 =
              let uu____10549 =
                let uu____10551 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____10551
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____10549)
               in
            FStar_Errors.raise_error uu____10543 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____10573 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____10573
       then
         let uu____10578 = FStar_Syntax_Print.term_to_string t  in
         let uu____10580 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____10578 uu____10580
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____10589 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____10589
        then
          let uu____10594 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____10594
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____10603 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____10603
         then
           let uu____10608 = FStar_Syntax_Print.term_to_string t  in
           let uu____10610 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____10608 uu____10610
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
        let uu____10694 =
          let uu____10696 =
            FStar_Util.for_all
              (fun uu____10710  ->
                 match uu____10710 with
                 | (uu____10720,uu____10721,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____10696  in
        if uu____10694
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____10773 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____10773
              then
                let uu____10776 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____10776
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____10783 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____10783
               then
                 let uu____10786 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____10786
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____10804 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____10804 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____10838 =
             match uu____10838 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____10875 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____10875
                   then
                     let uu____10880 =
                       let uu____10882 =
                         let uu____10886 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____10886
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____10882
                         (FStar_String.concat ", ")
                        in
                     let uu____10934 =
                       let uu____10936 =
                         let uu____10940 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____10940
                           (FStar_List.map
                              (fun u  ->
                                 let uu____10953 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____10955 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____10953
                                   uu____10955))
                          in
                       FStar_All.pipe_right uu____10936
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____10880
                       uu____10934
                   else ());
                  (let univs2 =
                     let uu____10969 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____10981 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____10981) univs1
                       uu____10969
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____10988 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____10988
                    then
                      let uu____10993 =
                        let uu____10995 =
                          let uu____10999 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____10999
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____10995
                          (FStar_String.concat ", ")
                         in
                      let uu____11047 =
                        let uu____11049 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____11063 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____11065 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____11063
                                    uu____11065))
                           in
                        FStar_All.pipe_right uu____11049
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____10993 uu____11047
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____11086 =
             let uu____11103 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____11103  in
           match uu____11086 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____11193 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____11193
                 then ()
                 else
                   (let uu____11198 = lec_hd  in
                    match uu____11198 with
                    | (lb1,uu____11206,uu____11207) ->
                        let uu____11208 = lec2  in
                        (match uu____11208 with
                         | (lb2,uu____11216,uu____11217) ->
                             let msg =
                               let uu____11220 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____11222 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____11220 uu____11222
                                in
                             let uu____11225 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____11225))
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
                 let uu____11293 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____11293
                 then ()
                 else
                   (let uu____11298 = lec_hd  in
                    match uu____11298 with
                    | (lb1,uu____11306,uu____11307) ->
                        let uu____11308 = lec2  in
                        (match uu____11308 with
                         | (lb2,uu____11316,uu____11317) ->
                             let msg =
                               let uu____11320 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____11322 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____11320 uu____11322
                                in
                             let uu____11325 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____11325))
                  in
               let lecs1 =
                 let uu____11336 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____11389 = univs_and_uvars_of_lec this_lec  in
                        match uu____11389 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____11336 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____11494 = lec_hd  in
                   match uu____11494 with
                   | (lbname,e,c) ->
                       let uu____11504 =
                         let uu____11510 =
                           let uu____11512 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____11514 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____11516 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____11512 uu____11514 uu____11516
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____11510)
                          in
                       let uu____11520 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____11504 uu____11520
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____11539 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____11539 with
                         | FStar_Pervasives_Native.Some uu____11548 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____11556 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____11560 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____11560 with
                              | (bs,kres) ->
                                  ((let uu____11604 =
                                      let uu____11605 =
                                        let uu____11608 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____11608
                                         in
                                      uu____11605.FStar_Syntax_Syntax.n  in
                                    match uu____11604 with
                                    | FStar_Syntax_Syntax.Tm_type uu____11609
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____11613 =
                                          let uu____11615 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____11615  in
                                        if uu____11613
                                        then fail1 kres
                                        else ()
                                    | uu____11620 -> fail1 kres);
                                   (let a =
                                      let uu____11622 =
                                        let uu____11625 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _11628  ->
                                             FStar_Pervasives_Native.Some
                                               _11628) uu____11625
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____11622
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____11636 ->
                                          let uu____11645 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____11645
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
                      (fun uu____11748  ->
                         match uu____11748 with
                         | (lbname,e,c) ->
                             let uu____11794 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____11855 ->
                                   let uu____11868 = (e, c)  in
                                   (match uu____11868 with
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
                                                (fun uu____11908  ->
                                                   match uu____11908 with
                                                   | (x,uu____11914) ->
                                                       let uu____11915 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____11915)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____11933 =
                                                let uu____11935 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____11935
                                                 in
                                              if uu____11933
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
                                          let uu____11944 =
                                            let uu____11945 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____11945.FStar_Syntax_Syntax.n
                                             in
                                          match uu____11944 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____11970 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____11970 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____11981 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____11985 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____11985, gen_tvars))
                                in
                             (match uu____11794 with
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
        (let uu____12132 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____12132
         then
           let uu____12135 =
             let uu____12137 =
               FStar_List.map
                 (fun uu____12152  ->
                    match uu____12152 with
                    | (lb,uu____12161,uu____12162) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____12137 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____12135
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____12188  ->
                match uu____12188 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____12217 = gen env is_rec lecs  in
           match uu____12217 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____12316  ->
                       match uu____12316 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____12378 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____12378
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____12426  ->
                           match uu____12426 with
                           | (l,us,e,c,gvs) ->
                               let uu____12460 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____12462 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____12464 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____12466 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____12468 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____12460 uu____12462 uu____12464
                                 uu____12466 uu____12468))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____12513  ->
                match uu____12513 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____12557 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____12557, t, c, gvs)) univnames_lecs
           generalized_lecs)
  
let (check_and_ascribe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t))
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
              (let uu____12618 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____12618 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____12624 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _12627  -> FStar_Pervasives_Native.Some _12627)
                     uu____12624)
             in
          let is_var e1 =
            let uu____12635 =
              let uu____12636 = FStar_Syntax_Subst.compress e1  in
              uu____12636.FStar_Syntax_Syntax.n  in
            match uu____12635 with
            | FStar_Syntax_Syntax.Tm_name uu____12640 -> true
            | uu____12642 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1516_12663 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1516_12663.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1516_12663.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____12664 -> e2  in
          let env2 =
            let uu___1519_12666 = env1  in
            let uu____12667 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1519_12666.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1519_12666.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1519_12666.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1519_12666.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1519_12666.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1519_12666.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1519_12666.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1519_12666.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1519_12666.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1519_12666.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1519_12666.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1519_12666.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1519_12666.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1519_12666.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1519_12666.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1519_12666.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1519_12666.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____12667;
              FStar_TypeChecker_Env.is_iface =
                (uu___1519_12666.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1519_12666.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1519_12666.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1519_12666.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1519_12666.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1519_12666.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1519_12666.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1519_12666.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1519_12666.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1519_12666.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1519_12666.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1519_12666.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1519_12666.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1519_12666.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1519_12666.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1519_12666.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1519_12666.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1519_12666.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1519_12666.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1519_12666.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1519_12666.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1519_12666.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1519_12666.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1519_12666.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1519_12666.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1519_12666.FStar_TypeChecker_Env.strict_args_tab)
            }  in
          let uu____12669 = check1 env2 t1 t2  in
          match uu____12669 with
          | FStar_Pervasives_Native.None  ->
              let uu____12676 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____12682 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____12676 uu____12682
          | FStar_Pervasives_Native.Some g ->
              ((let uu____12689 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12689
                then
                  let uu____12694 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____12694
                else ());
               (let uu____12700 = decorate e t2  in (uu____12700, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp -> (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____12728 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____12728
         then
           let uu____12731 = FStar_Syntax_Print.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____12731
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_Syntax_Util.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____12745 = FStar_Syntax_Util.is_total_lcomp lc  in
         if uu____12745
         then
           let uu____12753 = discharge g1  in
           let uu____12755 = FStar_Syntax_Syntax.lcomp_comp lc  in
           (uu____12753, uu____12755)
         else
           (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
            let steps =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.NoFullNorm;
              FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
            let c1 =
              let uu____12764 =
                let uu____12765 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                FStar_All.pipe_right uu____12765 FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____12764
                (FStar_TypeChecker_Normalize.normalize_comp steps env)
               in
            let uu____12766 = check_trivial_precondition env c1  in
            match uu____12766 with
            | (ct,vc,g2) ->
                ((let uu____12782 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Simplification")
                     in
                  if uu____12782
                  then
                    let uu____12787 = FStar_Syntax_Print.term_to_string vc
                       in
                    FStar_Util.print1 "top-level VC: %s\n" uu____12787
                  else ());
                 (let uu____12792 = discharge g2  in
                  let uu____12794 =
                    FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp  in
                  (uu____12792, uu____12794)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_12828 =
        match uu___8_12828 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____12838)::[] -> f fst1
        | uu____12863 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____12875 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____12875
          (fun _12876  -> FStar_TypeChecker_Common.NonTrivial _12876)
         in
      let op_or_e e =
        let uu____12887 =
          let uu____12888 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____12888  in
        FStar_All.pipe_right uu____12887
          (fun _12891  -> FStar_TypeChecker_Common.NonTrivial _12891)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _12898  -> FStar_TypeChecker_Common.NonTrivial _12898)
         in
      let op_or_t t =
        let uu____12909 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____12909
          (fun _12912  -> FStar_TypeChecker_Common.NonTrivial _12912)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _12919  -> FStar_TypeChecker_Common.NonTrivial _12919)
         in
      let short_op_ite uu___9_12925 =
        match uu___9_12925 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____12935)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____12962)::[] ->
            let uu____13003 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____13003
              (fun _13004  -> FStar_TypeChecker_Common.NonTrivial _13004)
        | uu____13005 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____13017 =
          let uu____13025 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____13025)  in
        let uu____13033 =
          let uu____13043 =
            let uu____13051 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____13051)  in
          let uu____13059 =
            let uu____13069 =
              let uu____13077 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____13077)  in
            let uu____13085 =
              let uu____13095 =
                let uu____13103 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____13103)  in
              let uu____13111 =
                let uu____13121 =
                  let uu____13129 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____13129)  in
                [uu____13121; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____13095 :: uu____13111  in
            uu____13069 :: uu____13085  in
          uu____13043 :: uu____13059  in
        uu____13017 :: uu____13033  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____13191 =
            FStar_Util.find_map table
              (fun uu____13206  ->
                 match uu____13206 with
                 | (x,mk1) ->
                     let uu____13223 = FStar_Ident.lid_equals x lid  in
                     if uu____13223
                     then
                       let uu____13228 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____13228
                     else FStar_Pervasives_Native.None)
             in
          (match uu____13191 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____13232 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____13240 =
      let uu____13241 = FStar_Syntax_Util.un_uinst l  in
      uu____13241.FStar_Syntax_Syntax.n  in
    match uu____13240 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____13246 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____13282)::uu____13283 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____13302 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____13311,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____13312))::uu____13313 -> bs
      | uu____13331 ->
          let uu____13332 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____13332 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____13336 =
                 let uu____13337 = FStar_Syntax_Subst.compress t  in
                 uu____13337.FStar_Syntax_Syntax.n  in
               (match uu____13336 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____13341) ->
                    let uu____13362 =
                      FStar_Util.prefix_until
                        (fun uu___10_13402  ->
                           match uu___10_13402 with
                           | (uu____13410,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____13411)) ->
                               false
                           | uu____13416 -> true) bs'
                       in
                    (match uu____13362 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____13452,uu____13453) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____13525,uu____13526) ->
                         let uu____13599 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____13619  ->
                                   match uu____13619 with
                                   | (x,uu____13628) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____13599
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____13677  ->
                                     match uu____13677 with
                                     | (x,i) ->
                                         let uu____13696 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____13696, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____13707 -> bs))
  
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
            let uu____13736 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____13736
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
          let uu____13767 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____13767
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
        (let uu____13810 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____13810
         then
           ((let uu____13815 = FStar_Ident.text_of_lid lident  in
             d uu____13815);
            (let uu____13817 = FStar_Ident.text_of_lid lident  in
             let uu____13819 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____13817 uu____13819))
         else ());
        (let fv =
           let uu____13825 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____13825
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
         let uu____13837 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1674_13839 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1674_13839.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1674_13839.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1674_13839.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1674_13839.FStar_Syntax_Syntax.sigattrs)
           }), uu____13837))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_13857 =
        match uu___11_13857 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____13860 -> false  in
      let reducibility uu___12_13868 =
        match uu___12_13868 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____13875 -> false  in
      let assumption uu___13_13883 =
        match uu___13_13883 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____13887 -> false  in
      let reification uu___14_13895 =
        match uu___14_13895 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____13898 -> true
        | uu____13900 -> false  in
      let inferred uu___15_13908 =
        match uu___15_13908 with
        | FStar_Syntax_Syntax.Discriminator uu____13910 -> true
        | FStar_Syntax_Syntax.Projector uu____13912 -> true
        | FStar_Syntax_Syntax.RecordType uu____13918 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____13928 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____13941 -> false  in
      let has_eq uu___16_13949 =
        match uu___16_13949 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____13953 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____14032 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____14039 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____14050 =
        let uu____14052 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___17_14058  ->
                  match uu___17_14058 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____14061 -> false))
           in
        FStar_All.pipe_right uu____14052 Prims.op_Negation  in
      if uu____14050
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____14082 =
            let uu____14088 =
              let uu____14090 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____14090 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____14088)  in
          FStar_Errors.raise_error uu____14082 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____14108 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____14116 =
            let uu____14118 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____14118  in
          if uu____14116 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____14128),uu____14129) ->
              ((let uu____14141 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____14141
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____14150 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____14150
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____14161 ->
              let uu____14170 =
                let uu____14172 =
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
                Prims.op_Negation uu____14172  in
              if uu____14170 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____14182 ->
              let uu____14189 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____14189 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____14197 ->
              let uu____14204 =
                let uu____14206 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____14206  in
              if uu____14204 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14216 ->
              let uu____14217 =
                let uu____14219 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____14219  in
              if uu____14217 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14229 ->
              let uu____14230 =
                let uu____14232 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____14232  in
              if uu____14230 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____14242 ->
              let uu____14255 =
                let uu____14257 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____14257  in
              if uu____14255 then err'1 () else ()
          | uu____14267 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let has_erased_for_extraction_attr fv =
        let uu____14290 =
          let uu____14295 =
            FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
          FStar_All.pipe_right uu____14295
            (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
           in
        FStar_All.pipe_right uu____14290
          (fun l_opt  ->
             (FStar_Util.is_some l_opt) &&
               (let uu____14314 = FStar_All.pipe_right l_opt FStar_Util.must
                   in
                FStar_All.pipe_right uu____14314
                  (FStar_List.existsb
                     (fun t1  ->
                        let uu____14332 =
                          let uu____14333 = FStar_Syntax_Subst.compress t1
                             in
                          uu____14333.FStar_Syntax_Syntax.n  in
                        match uu____14332 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            FStar_Ident.lid_equals
                              (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              FStar_Parser_Const.must_erase_for_extraction_attr
                            -> true
                        | uu____14339 -> false))))
         in
      let rec aux_whnf env t1 =
        let uu____14365 =
          let uu____14366 = FStar_Syntax_Subst.compress t1  in
          uu____14366.FStar_Syntax_Syntax.n  in
        match uu____14365 with
        | FStar_Syntax_Syntax.Tm_type uu____14370 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (has_erased_for_extraction_attr fv)
        | FStar_Syntax_Syntax.Tm_arrow uu____14373 ->
            let uu____14388 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____14388 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____14421 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____14421
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____14427;
               FStar_Syntax_Syntax.index = uu____14428;
               FStar_Syntax_Syntax.sort = t2;_},uu____14430)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14439,uu____14440) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____14482::[]) ->
            let uu____14521 =
              let uu____14522 = FStar_Syntax_Util.un_uinst head1  in
              uu____14522.FStar_Syntax_Syntax.n  in
            (match uu____14521 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.erased_lid)
                   || (has_erased_for_extraction_attr fv)
             | uu____14527 -> false)
        | uu____14529 -> false
      
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
        (let uu____14539 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____14539
         then
           let uu____14544 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____14544
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
                (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun r  ->
      fun eff_name  ->
        fun signature_ts  ->
          fun repr_ts  ->
            fun u  ->
              fun a_tm  ->
                let fail1 t =
                  let uu____14605 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____14605 r  in
                let uu____14615 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____14615 with
                | (uu____14624,signature) ->
                    let uu____14626 =
                      let uu____14627 = FStar_Syntax_Subst.compress signature
                         in
                      uu____14627.FStar_Syntax_Syntax.n  in
                    (match uu____14626 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14635) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____14683 =
                                FStar_List.fold_left
                                  (fun uu____14722  ->
                                     fun uu____14723  ->
                                       match (uu____14722, uu____14723) with
                                       | ((is,g,substs),(b,uu____14770)) ->
                                           let uu____14799 =
                                             let uu____14812 =
                                               FStar_Syntax_Subst.subst
                                                 substs
                                                 b.FStar_Syntax_Syntax.sort
                                                in
                                             new_implicit_var "" r env
                                               uu____14812
                                              in
                                           (match uu____14799 with
                                            | (t,uu____14825,g_t) ->
                                                let uu____14839 =
                                                  FStar_TypeChecker_Env.conj_guard
                                                    g g_t
                                                   in
                                                ((FStar_List.append is [t]),
                                                  uu____14839,
                                                  (FStar_List.append substs
                                                     [FStar_Syntax_Syntax.NT
                                                        (b, t)]))))
                                  ([], FStar_TypeChecker_Env.trivial_guard,
                                    [FStar_Syntax_Syntax.NT
                                       ((FStar_Pervasives_Native.fst a),
                                         a_tm)]) bs2
                                 in
                              (match uu____14683 with
                               | (is,g,uu____14860) ->
                                   let repr =
                                     let uu____14870 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts [u]
                                        in
                                     FStar_All.pipe_right uu____14870
                                       FStar_Pervasives_Native.snd
                                      in
                                   let uu____14879 =
                                     let uu____14880 =
                                       let uu____14885 =
                                         FStar_List.map
                                           FStar_Syntax_Syntax.as_arg (a_tm
                                           :: is)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr
                                         uu____14885
                                        in
                                     uu____14880 FStar_Pervasives_Native.None
                                       r
                                      in
                                   (uu____14879, g))
                          | uu____14894 -> fail1 signature)
                     | uu____14895 -> fail1 signature)
  
let (fresh_layered_effect_repr_en :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.universe ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t))
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
  