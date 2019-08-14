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
    (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option *
      FStar_TypeChecker_Common.guard_t))
  =
  fun lc  ->
    let uu____984 =
      FStar_All.pipe_right lc FStar_TypeChecker_Common.lcomp_comp  in
    FStar_All.pipe_right uu____984
      (fun uu____1012  ->
         match uu____1012 with | (c,g) -> ((comp_univ_opt c), g))
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____1053)::[] -> wp
      | uu____1078 ->
          let uu____1089 =
            let uu____1091 =
              let uu____1093 =
                FStar_List.map
                  (fun uu____1107  ->
                     match uu____1107 with
                     | (x,uu____1116) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____1093 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____1091
             in
          failwith uu____1089
       in
    let uu____1127 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____1127, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____1144 = destruct_comp c  in
        match uu____1144 with
        | (u,uu____1152,wp) ->
            let uu____1154 =
              let uu____1165 =
                let uu____1174 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____1174  in
              [uu____1165]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____1154;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____1207 =
          let uu____1214 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____1215 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____1214 uu____1215  in
        match uu____1207 with | (m,uu____1217,uu____1218) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____1235 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2)
           in
        if uu____1235
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
        let uu____1282 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____1282 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____1319 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____1319 with
             | (a,kwp) ->
                 let uu____1350 = destruct_comp m1  in
                 let uu____1357 = destruct_comp m2  in
                 ((md, a, kwp), uu____1350, uu____1357))
  
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
        let uu____1407 =
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name eff_name
           in
        if uu____1407
        then (c, FStar_TypeChecker_Common.trivial_guard)
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
              let uu____1424 =
                FStar_TypeChecker_Env.monad_leq env
                  src_ed.FStar_Syntax_Syntax.mname
                  dst_ed.FStar_Syntax_Syntax.mname
                 in
              match uu____1424 with
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
            let uu____1432 = destruct_comp ct  in
            match uu____1432 with
            | (u,a,wp) ->
                let uu____1446 =
                  FStar_TypeChecker_Env.inst_tscheme_with lift_t [u]  in
                (match uu____1446 with
                 | (uu____1455,lift_t1) ->
                     let uu____1457 =
                       let uu____1470 =
                         let uu____1471 = FStar_Syntax_Subst.compress lift_t1
                            in
                         uu____1471.FStar_Syntax_Syntax.n  in
                       match uu____1470 with
                       | FStar_Syntax_Syntax.Tm_arrow (bs,c1) ->
                           let uu____1508 =
                             FStar_Syntax_Subst.open_comp bs c1  in
                           FStar_All.pipe_right uu____1508
                             (fun uu____1525  ->
                                match uu____1525 with
                                | (bs1,c2) ->
                                    let uu____1536 =
                                      FStar_Syntax_Util.comp_to_comp_typ c2
                                       in
                                    (bs1, uu____1536))
                       | uu____1537 ->
                           let uu____1538 =
                             let uu____1540 =
                               let uu____1542 =
                                 FStar_Syntax_Print.term_to_string lift_t1
                                  in
                               Prims.op_Hat uu____1542
                                 " is not an arrow type"
                                in
                             Prims.op_Hat "lift_t: " uu____1540  in
                           failwith uu____1538
                        in
                     (match uu____1457 with
                      | (lift_bs,lift_ct) ->
                          let uu____1580 =
                            match lift_bs with
                            | a_b::wp_b::bs when
                                (FStar_List.length bs) >= Prims.int_one ->
                                let uu____1675 =
                                  let uu____1684 =
                                    FStar_List.splitAt
                                      ((FStar_List.length bs) - Prims.int_one)
                                      bs
                                     in
                                  FStar_All.pipe_right uu____1684
                                    FStar_Pervasives_Native.fst
                                   in
                                (a_b, wp_b, uu____1675)
                            | uu____1782 ->
                                let uu____1791 =
                                  let uu____1793 =
                                    let uu____1795 =
                                      FStar_Syntax_Print.term_to_string
                                        lift_t1
                                       in
                                    Prims.op_Hat uu____1795
                                      " does not have enough binders"
                                     in
                                  Prims.op_Hat "lift_t: " uu____1793  in
                                failwith uu____1791
                             in
                          (match uu____1580 with
                           | (a_b,wp_b,rest_bs) ->
                               let uu____1872 =
                                 let uu____1879 =
                                   let uu____1880 =
                                     FStar_Syntax_Subst.compress
                                       lift_ct.FStar_Syntax_Syntax.result_typ
                                      in
                                   uu____1880.FStar_Syntax_Syntax.n  in
                                 match uu____1879 with
                                 | FStar_Syntax_Syntax.Tm_app
                                     (uu____1889,uu____1890::is) ->
                                     let uu____1932 =
                                       FStar_List.map
                                         FStar_Pervasives_Native.fst is
                                        in
                                     ((lift_ct.FStar_Syntax_Syntax.comp_univs),
                                       uu____1932)
                                 | uu____1949 ->
                                     let uu____1950 =
                                       let uu____1952 =
                                         let uu____1954 =
                                           FStar_Syntax_Print.term_to_string
                                             lift_t1
                                            in
                                         Prims.op_Hat uu____1954
                                           " does not have a repr return type"
                                          in
                                       Prims.op_Hat "lift_t: " uu____1952  in
                                     failwith uu____1950
                                  in
                               (match uu____1872 with
                                | (u_m,is) ->
                                    let uu____1974 =
                                      let uu____1983 =
                                        let uu____1992 =
                                          let uu____2001 =
                                            FStar_TypeChecker_Env.push_binders
                                              env [a_b; wp_b]
                                             in
                                          (uu____2001, [],
                                            FStar_TypeChecker_Common.trivial_guard)
                                           in
                                        FStar_List.fold_left
                                          (fun uu____2047  ->
                                             fun b  ->
                                               match uu____2047 with
                                               | (env1,is_uvars,g) ->
                                                   let uu____2078 =
                                                     FStar_TypeChecker_Env.new_implicit_var_aux
                                                       ""
                                                       FStar_Range.dummyRange
                                                       env1
                                                       (FStar_Pervasives_Native.fst
                                                          b).FStar_Syntax_Syntax.sort
                                                       FStar_Syntax_Syntax.Strict
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   (match uu____2078 with
                                                    | (t,uu____2107,g_t) ->
                                                        let uu____2121 =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env1 [b]
                                                           in
                                                        let uu____2134 =
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g g_t
                                                           in
                                                        (uu____2121,
                                                          (FStar_List.append
                                                             is_uvars 
                                                             [t]),
                                                          uu____2134)))
                                          uu____1992 rest_bs
                                         in
                                      match uu____1983 with
                                      | (uu____2145,rest_bs_uvars,g) ->
                                          (rest_bs_uvars, g)
                                       in
                                    (match uu____1974 with
                                     | (rest_bs_uvars,g) ->
                                         let subst_for_is =
                                           FStar_List.map2
                                             (fun b  ->
                                                fun t  ->
                                                  let uu____2194 =
                                                    let uu____2201 =
                                                      FStar_All.pipe_right b
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    (uu____2201, t)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____2194) (a_b :: wp_b
                                             :: rest_bs) (a :: wp ::
                                             rest_bs_uvars)
                                            in
                                         let is1 =
                                           FStar_List.map
                                             (FStar_Syntax_Subst.subst
                                                subst_for_is) is
                                            in
                                         let uu____2231 =
                                           let uu____2232 =
                                             let uu____2233 =
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
                                                 = uu____2233;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____2232
                                            in
                                         (uu____2231, g))))))))
  
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
            let uu____2312 =
              let uu____2313 =
                let uu____2324 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____2324]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____2313;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____2312
  
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
          let uu____2408 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____2408
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2420 =
      let uu____2421 = FStar_Syntax_Subst.compress t  in
      uu____2421.FStar_Syntax_Syntax.n  in
    match uu____2420 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2425 -> true
    | uu____2441 -> false
  
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
              let uu____2511 =
                let uu____2513 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____2513  in
              if uu____2511
              then f
              else (let uu____2520 = reason1 ()  in label uu____2520 r f)
  
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
            let uu___314_2541 = g  in
            let uu____2542 =
              let uu____2543 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____2543  in
            {
              FStar_TypeChecker_Common.guard_f = uu____2542;
              FStar_TypeChecker_Common.deferred =
                (uu___314_2541.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___314_2541.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___314_2541.FStar_TypeChecker_Common.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2564 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____2564
        then c
        else
          (let uu____2569 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____2569
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let uu____2610 =
                  FStar_Syntax_Util.get_match_with_close_wps
                    md.FStar_Syntax_Syntax.match_wps
                   in
                match uu____2610 with
                | (uu____2619,uu____2620,close1) ->
                    FStar_List.fold_right
                      (fun x  ->
                         fun wp  ->
                           let bs =
                             let uu____2643 = FStar_Syntax_Syntax.mk_binder x
                                in
                             [uu____2643]  in
                           let us =
                             let uu____2665 =
                               let uu____2668 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               [uu____2668]  in
                             u_res :: uu____2665  in
                           let wp1 =
                             FStar_Syntax_Util.abs bs wp
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None
                                     [FStar_Syntax_Syntax.TOTAL]))
                              in
                           let uu____2674 =
                             let uu____2679 =
                               FStar_TypeChecker_Env.inst_effect_fun_with us
                                 env md close1
                                in
                             let uu____2680 =
                               let uu____2681 =
                                 FStar_Syntax_Syntax.as_arg res_t  in
                               let uu____2690 =
                                 let uu____2701 =
                                   FStar_Syntax_Syntax.as_arg
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let uu____2710 =
                                   let uu____2721 =
                                     FStar_Syntax_Syntax.as_arg wp1  in
                                   [uu____2721]  in
                                 uu____2701 :: uu____2710  in
                               uu____2681 :: uu____2690  in
                             FStar_Syntax_Syntax.mk_Tm_app uu____2679
                               uu____2680
                              in
                           uu____2674 FStar_Pervasives_Native.None
                             wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____2763 = destruct_comp c1  in
              match uu____2763 with
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
        let bs =
          FStar_All.pipe_right bvs
            (FStar_List.map FStar_Syntax_Syntax.mk_binder)
           in
        FStar_All.pipe_right lc
          (FStar_TypeChecker_Common.apply_lcomp (close_comp env bvs)
             (fun g  ->
                let uu____2803 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____2803
                  (close_guard_implicits env bs)))
  
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
              ({ FStar_Syntax_Syntax.ppname = uu____2826;
                 FStar_Syntax_Syntax.index = uu____2827;
                 FStar_Syntax_Syntax.sort =
                   { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____2829;
                     FStar_Syntax_Syntax.vars = uu____2830;_};_},uu____2831)
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
              close_comp env [x] c
          | uu____2839 -> c
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_2851  ->
            match uu___0_2851 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____2854 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____2879 =
            let uu____2882 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____2882 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____2879
            (fun c  ->
               (let uu____2938 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____2938) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____2942 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____2942)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____2953 = FStar_Syntax_Util.head_and_args' e  in
                match uu____2953 with
                | (head1,uu____2970) ->
                    let uu____2991 =
                      let uu____2992 = FStar_Syntax_Util.un_uinst head1  in
                      uu____2992.FStar_Syntax_Syntax.n  in
                    (match uu____2991 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2997 =
                           let uu____2999 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____2999
                            in
                         Prims.op_Negation uu____2997
                     | uu____3000 -> true)))
              &&
              (let uu____3003 = should_not_inline_lc lc  in
               Prims.op_Negation uu____3003)
  
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
            let uu____3031 =
              let uu____3033 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____3033  in
            if uu____3031
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____3040 = FStar_Syntax_Util.is_unit t  in
               if uu____3040
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
                    let uu____3049 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____3049
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____3054 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____3054 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____3064 =
                             let uu____3065 =
                               let uu____3070 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____3071 =
                                 let uu____3072 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____3081 =
                                   let uu____3092 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____3092]  in
                                 uu____3072 :: uu____3081  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____3070
                                 uu____3071
                                in
                             uu____3065 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____3064)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____3126 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____3126
           then
             let uu____3131 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____3133 = FStar_Syntax_Print.term_to_string v1  in
             let uu____3135 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____3131 uu____3133 uu____3135
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
                let uu____3173 =
                  FStar_TypeChecker_Env.monad_leq env
                    FStar_Parser_Const.effect_PURE_lid
                    md.FStar_Syntax_Syntax.mname
                   in
                match uu____3173 with
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
              let uu____3179 =
                let uu____3184 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [FStar_Syntax_Syntax.U_zero; u_res_t] env md
                    md.FStar_Syntax_Syntax.bind_wp
                   in
                let uu____3185 =
                  let uu____3186 =
                    let uu____3195 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_range r))
                        FStar_Pervasives_Native.None r
                       in
                    FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3195
                     in
                  let uu____3204 =
                    let uu____3215 =
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        FStar_Syntax_Syntax.t_unit
                       in
                    let uu____3232 =
                      let uu____3243 = FStar_Syntax_Syntax.as_arg res_t  in
                      let uu____3252 =
                        let uu____3263 = FStar_Syntax_Syntax.as_arg wp11  in
                        let uu____3272 =
                          let uu____3283 =
                            let uu____3292 =
                              let uu____3293 =
                                let uu____3294 =
                                  FStar_Syntax_Syntax.null_binder
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                [uu____3294]  in
                              FStar_Syntax_Util.abs uu____3293 wp2
                                (FStar_Pervasives_Native.Some
                                   (FStar_Syntax_Util.mk_residual_comp
                                      FStar_Parser_Const.effect_Tot_lid
                                      FStar_Pervasives_Native.None
                                      [FStar_Syntax_Syntax.TOTAL]))
                               in
                            FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                              uu____3292
                             in
                          [uu____3283]  in
                        uu____3263 :: uu____3272  in
                      uu____3243 :: uu____3252  in
                    uu____3215 :: uu____3232  in
                  uu____3186 :: uu____3204  in
                FStar_Syntax_Syntax.mk_Tm_app uu____3184 uu____3185  in
              uu____3179 FStar_Pervasives_Native.None
                wp2.FStar_Syntax_Syntax.pos
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____3383 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_3389  ->
              match uu___1_3389 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____3392 -> false))
       in
    if uu____3383
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_3404  ->
              match uu___2_3404 with
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
        let uu____3424 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____3424
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____3430 = destruct_comp c1  in
           match uu____3430 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let r = FStar_TypeChecker_Env.get_range env  in
               let pure_assume_wp =
                 let uu____3443 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assume_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____3443  in
               let pure_assume_wp1 =
                 let uu____3448 =
                   let uu____3453 =
                     let uu____3454 =
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula
                        in
                     [uu____3454]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____3453
                    in
                 uu____3448 FStar_Pervasives_Native.None r  in
               let w_wp =
                 lift_wp_and_bind_with env pure_assume_wp1 md u_res_t res_t
                   wp
                  in
               let uu____3488 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t w_wp uu____3488)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3516 =
          let uu____3517 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____3517 with
          | (c,g_c) ->
              let uu____3528 =
                let uu____3529 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                   in
                if uu____3529
                then c
                else
                  (match f with
                   | FStar_TypeChecker_Common.Trivial  -> c
                   | FStar_TypeChecker_Common.NonTrivial f1 ->
                       weaken_comp env c f1)
                 in
              (uu____3528, g_c)
           in
        let uu____3535 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____3535 weaken
  
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
               let uu____3584 = destruct_comp c1  in
               match uu____3584 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let pure_assert_wp =
                     let uu____3596 =
                       FStar_Syntax_Syntax.lid_as_fv
                         FStar_Parser_Const.pure_assert_wp_lid
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____3596  in
                   let pure_assert_wp1 =
                     let uu____3601 =
                       let uu____3606 =
                         let uu____3607 =
                           let uu____3616 = label_opt env reason r f  in
                           FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                             uu____3616
                            in
                         [uu____3607]  in
                       FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp
                         uu____3606
                        in
                     uu____3601 FStar_Pervasives_Native.None r  in
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
            let uu____3687 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____3687
            then (lc, g0)
            else
              (let flags =
                 let uu____3699 =
                   let uu____3707 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____3707
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____3699 with
                 | (maybe_trivial_post,flags) ->
                     let uu____3737 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_3745  ->
                               match uu___3_3745 with
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
                               | uu____3748 -> []))
                        in
                     FStar_List.append flags uu____3737
                  in
               let strengthen uu____3758 =
                 let uu____3759 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____3759 with
                 | (c,g_c) ->
                     let uu____3770 =
                       if env.FStar_TypeChecker_Env.lax
                       then c
                       else
                         (let g01 =
                            FStar_TypeChecker_Rel.simplify_guard env g0  in
                          let uu____3775 =
                            FStar_TypeChecker_Env.guard_form g01  in
                          match uu____3775 with
                          | FStar_TypeChecker_Common.Trivial  -> c
                          | FStar_TypeChecker_Common.NonTrivial f ->
                              ((let uu____3778 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    FStar_Options.Extreme
                                   in
                                if uu____3778
                                then
                                  let uu____3782 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env e_for_debugging_only
                                     in
                                  let uu____3784 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env f
                                     in
                                  FStar_Util.print2
                                    "-------------Strengthening pre-condition of term %s with guard %s\n"
                                    uu____3782 uu____3784
                                else ());
                               strengthen_comp env reason c f flags))
                        in
                     (uu____3770, g_c)
                  in
               let uu____3789 =
                 let uu____3790 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____3790
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____3789,
                 (let uu___496_3792 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___496_3792.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___496_3792.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___496_3792.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_3801  ->
            match uu___4_3801 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____3805 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____3834 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____3834
          then e
          else
            (let uu____3841 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____3844 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____3844)
                in
             if uu____3841
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
          fun uu____3897  ->
            match uu____3897 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____3917 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____3917 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____3930 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____3930
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____3940 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____3940
                       then
                         let uu____3945 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____3945
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____3952 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____3952
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____3961 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____3961
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____3968 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____3968
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____3984 =
                  let uu____3985 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____3985
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____3993 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____3993, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____3996 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____3996 with
                     | (c1,g_c1) ->
                         let uu____4007 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____4007 with
                          | (c2,g_c2) ->
                              (debug1
                                 (fun uu____4027  ->
                                    let uu____4028 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____4030 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____4035 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____4028 uu____4030 uu____4035);
                               (let aux uu____4053 =
                                  let uu____4054 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____4054
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____4085
                                        ->
                                        let uu____4086 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____4086
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____4118 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____4118
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____4163 =
                                  let uu____4164 =
                                    let uu____4166 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____4166  in
                                  if uu____4164
                                  then
                                    let uu____4180 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____4180
                                     then
                                       FStar_Util.Inl
                                         (c2,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____4203 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____4203))
                                  else
                                    (let uu____4218 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____4218
                                     then
                                       let close1 x reason c =
                                         let x1 =
                                           let uu___566_4260 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___566_4260.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___566_4260.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           }  in
                                         let uu____4261 =
                                           let uu____4267 =
                                             close_comp_if_refinement_t env
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c
                                              in
                                           (uu____4267, reason)  in
                                         FStar_Util.Inl uu____4261  in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some
                                          e,FStar_Pervasives_Native.Some x)
                                           ->
                                           let uu____4303 =
                                             FStar_All.pipe_right c2
                                               (FStar_Syntax_Subst.subst_comp
                                                  [FStar_Syntax_Syntax.NT
                                                     (x, e)])
                                              in
                                           FStar_All.pipe_right uu____4303
                                             (close1 x "c1 Tot")
                                       | (uu____4317,FStar_Pervasives_Native.Some
                                          x) ->
                                           FStar_All.pipe_right c2
                                             (close1 x "c1 Tot only close")
                                       | (uu____4340,uu____4341) -> aux ()
                                     else
                                       (let uu____4356 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____4356
                                        then
                                          let uu____4369 =
                                            let uu____4375 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____4375, "both GTot")  in
                                          FStar_Util.Inl uu____4369
                                        else aux ()))
                                   in
                                let uu____4386 = try_simplify ()  in
                                match uu____4386 with
                                | FStar_Util.Inl (c,reason) ->
                                    (debug1
                                       (fun uu____4416  ->
                                          let uu____4417 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____4417);
                                     (let uu____4420 =
                                        FStar_TypeChecker_Env.conj_guard g_c1
                                          g_c2
                                         in
                                      (c, uu____4420)))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____4432  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_layered_bind c11 b1 c21 =
                                        let uu____4466 =
                                          let c1_ed =
                                            FStar_TypeChecker_Env.get_effect_decl
                                              env
                                              (FStar_Syntax_Util.comp_effect_name
                                                 c11)
                                             in
                                          let c2_ed =
                                            FStar_TypeChecker_Env.get_effect_decl
                                              env
                                              (FStar_Syntax_Util.comp_effect_name
                                                 c21)
                                             in
                                          let uu____4479 =
                                            FStar_TypeChecker_Env.monad_leq
                                              env
                                              c1_ed.FStar_Syntax_Syntax.mname
                                              c2_ed.FStar_Syntax_Syntax.mname
                                             in
                                          match uu____4479 with
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____4492 =
                                                FStar_TypeChecker_Env.monad_leq
                                                  env
                                                  c2_ed.FStar_Syntax_Syntax.mname
                                                  c1_ed.FStar_Syntax_Syntax.mname
                                                 in
                                              (match uu____4492 with
                                               | FStar_Pervasives_Native.None
                                                    ->
                                                   failwith
                                                     (Prims.op_Hat
                                                        "Cannot bind "
                                                        (Prims.op_Hat
                                                           (c1_ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                           (Prims.op_Hat
                                                              " and "
                                                              (c2_ed.FStar_Syntax_Syntax.mname).FStar_Ident.str)))
                                               | FStar_Pervasives_Native.Some
                                                   ed ->
                                                   (c21, c2_ed, ed, c11,
                                                     c1_ed))
                                          | FStar_Pervasives_Native.Some ed
                                              -> (c11, c1_ed, ed, c21, c2_ed)
                                           in
                                        match uu____4466 with
                                        | (c12,uu____4524,uu____4525,c22,c2_ed)
                                            ->
                                            let uu____4528 =
                                              lift_to_layered_effect env c12
                                                c2_ed.FStar_Syntax_Syntax.mname
                                               in
                                            (match uu____4528 with
                                             | (c13,g_lift) ->
                                                 let uu____4539 =
                                                   let uu____4544 =
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                       c13
                                                      in
                                                   let uu____4545 =
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                       c22
                                                      in
                                                   (uu____4544, uu____4545)
                                                    in
                                                 (match uu____4539 with
                                                  | (ct1,ct2) ->
                                                      let uu____4552 =
                                                        let uu____4563 =
                                                          FStar_List.hd
                                                            ct1.FStar_Syntax_Syntax.comp_univs
                                                           in
                                                        let uu____4564 =
                                                          FStar_List.map
                                                            FStar_Pervasives_Native.fst
                                                            ct1.FStar_Syntax_Syntax.effect_args
                                                           in
                                                        (uu____4563,
                                                          (ct1.FStar_Syntax_Syntax.result_typ),
                                                          uu____4564)
                                                         in
                                                      (match uu____4552 with
                                                       | (u1,t1,is1) ->
                                                           let uu____4598 =
                                                             let uu____4609 =
                                                               FStar_List.hd
                                                                 ct2.FStar_Syntax_Syntax.comp_univs
                                                                in
                                                             let uu____4610 =
                                                               FStar_List.map
                                                                 FStar_Pervasives_Native.fst
                                                                 ct2.FStar_Syntax_Syntax.effect_args
                                                                in
                                                             (uu____4609,
                                                               (ct2.FStar_Syntax_Syntax.result_typ),
                                                               uu____4610)
                                                              in
                                                           (match uu____4598
                                                            with
                                                            | (u2,t2,is2) ->
                                                                let uu____4644
                                                                  =
                                                                  FStar_TypeChecker_Env.inst_tscheme_with
                                                                    c2_ed.FStar_Syntax_Syntax.bind_wp
                                                                    [u1; u2]
                                                                   in
                                                                (match uu____4644
                                                                 with
                                                                 | (uu____4653,bind_t)
                                                                    ->
                                                                    let uu____4655
                                                                    =
                                                                    let uu____4668
                                                                    =
                                                                    let uu____4669
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    bind_t
                                                                     in
                                                                    uu____4669.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____4668
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____4706
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    FStar_All.pipe_right
                                                                    uu____4706
                                                                    (fun
                                                                    uu____4723
                                                                     ->
                                                                    match uu____4723
                                                                    with
                                                                    | 
                                                                    (bs1,c3)
                                                                    ->
                                                                    let uu____4734
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    c3
                                                                    FStar_Syntax_Util.comp_to_comp_typ
                                                                     in
                                                                    (bs1,
                                                                    uu____4734))
                                                                    | 
                                                                    uu____4735
                                                                    ->
                                                                    let uu____4736
                                                                    =
                                                                    let uu____4738
                                                                    =
                                                                    let uu____4740
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____4740
                                                                    " is not an arrow"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "bind_t: "
                                                                    uu____4738
                                                                     in
                                                                    failwith
                                                                    uu____4736
                                                                     in
                                                                    (match uu____4655
                                                                    with
                                                                    | 
                                                                    (bind_bs,bind_ct)
                                                                    ->
                                                                    let uu____4778
                                                                    =
                                                                    match bind_bs
                                                                    with
                                                                    | 
                                                                    a_b::b_b::bs
                                                                    when
                                                                    (FStar_List.length
                                                                    bs) >=
                                                                    (Prims.of_int (2))
                                                                    ->
                                                                    let uu____4905
                                                                    =
                                                                    let uu____4932
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs) -
                                                                    (Prims.of_int (2)))
                                                                    bs  in
                                                                    FStar_All.pipe_right
                                                                    uu____4932
                                                                    (fun
                                                                    uu____5017
                                                                     ->
                                                                    match uu____5017
                                                                    with
                                                                    | 
                                                                    (l1,l2)
                                                                    ->
                                                                    let uu____5098
                                                                    =
                                                                    FStar_List.hd
                                                                    l2  in
                                                                    let uu____5111
                                                                    =
                                                                    let uu____5118
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                    FStar_List.hd
                                                                    uu____5118
                                                                     in
                                                                    (l1,
                                                                    uu____5098,
                                                                    uu____5111))
                                                                     in
                                                                    (match uu____4905
                                                                    with
                                                                    | 
                                                                    (rest_bs,f_b,g_b)
                                                                    ->
                                                                    (a_b,
                                                                    b_b,
                                                                    rest_bs,
                                                                    f_b, g_b))
                                                                    | 
                                                                    uu____5276
                                                                    ->
                                                                    let uu____5285
                                                                    =
                                                                    let uu____5287
                                                                    =
                                                                    let uu____5289
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____5289
                                                                    " does not have enough binders"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "bind_t: "
                                                                    uu____5287
                                                                     in
                                                                    failwith
                                                                    uu____5285
                                                                     in
                                                                    (match uu____4778
                                                                    with
                                                                    | 
                                                                    (a_b,b_b,rest_bs,f_b,g_b)
                                                                    ->
                                                                    let uu____5408
                                                                    =
                                                                    let uu____5415
                                                                    =
                                                                    let uu____5416
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    bind_ct.FStar_Syntax_Syntax.result_typ
                                                                     in
                                                                    uu____5416.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____5415
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____5425,uu____5426::is)
                                                                    ->
                                                                    let uu____5468
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    is  in
                                                                    ((bind_ct.FStar_Syntax_Syntax.comp_univs),
                                                                    uu____5468)
                                                                    | 
                                                                    uu____5485
                                                                    ->
                                                                    let uu____5486
                                                                    =
                                                                    let uu____5488
                                                                    =
                                                                    let uu____5490
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____5490
                                                                    " does not have repr return type"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "bind_t: "
                                                                    uu____5488
                                                                     in
                                                                    failwith
                                                                    uu____5486
                                                                     in
                                                                    (match uu____5408
                                                                    with
                                                                    | 
                                                                    (u_m,is)
                                                                    ->
                                                                    let uu____5510
                                                                    =
                                                                    let uu____5519
                                                                    =
                                                                    let uu____5528
                                                                    =
                                                                    let uu____5537
                                                                    =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env
                                                                    [a_b;
                                                                    b_b]  in
                                                                    (uu____5537,
                                                                    [],
                                                                    FStar_TypeChecker_Common.trivial_guard)
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____5583
                                                                     ->
                                                                    fun b2 
                                                                    ->
                                                                    match uu____5583
                                                                    with
                                                                    | 
                                                                    (env1,is_uvars,g)
                                                                    ->
                                                                    let uu____5614
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
                                                                    (match uu____5614
                                                                    with
                                                                    | 
                                                                    (t,uu____5643,g_t)
                                                                    ->
                                                                    let uu____5657
                                                                    =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env1 
                                                                    [b2]  in
                                                                    let uu____5670
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g g_t  in
                                                                    (uu____5657,
                                                                    (FStar_List.append
                                                                    is_uvars
                                                                    [t]),
                                                                    uu____5670)))
                                                                    uu____5528
                                                                    rest_bs
                                                                     in
                                                                    match uu____5519
                                                                    with
                                                                    | 
                                                                    (uu____5681,rest_bs_uvars,g)
                                                                    ->
                                                                    (rest_bs_uvars,
                                                                    g)  in
                                                                    (match uu____5510
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
                                                                    let uu____5730
                                                                    =
                                                                    let uu____5737
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    b2
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    (uu____5737,
                                                                    t)  in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____5730)
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
                                                                    let uu____5770
                                                                    =
                                                                    let uu____5771
                                                                    =
                                                                    let uu____5774
                                                                    =
                                                                    let uu____5775
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    f_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    uu____5775.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_Syntax_Subst.compress
                                                                    uu____5774
                                                                     in
                                                                    uu____5771.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____5770
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____5786,uu____5787::is4)
                                                                    ->
                                                                    let uu____5829
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is4
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5829
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1))
                                                                    | 
                                                                    uu____5862
                                                                    ->
                                                                    let uu____5863
                                                                    =
                                                                    let uu____5865
                                                                    =
                                                                    let uu____5867
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____5867
                                                                    " is not a repr type"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "Type of f in bind_t:"
                                                                    uu____5865
                                                                     in
                                                                    failwith
                                                                    uu____5863
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
                                                                    let uu____5890
                                                                    =
                                                                    let uu____5891
                                                                    =
                                                                    let uu____5894
                                                                    =
                                                                    let uu____5895
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    g_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    uu____5895.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_Syntax_Subst.compress
                                                                    uu____5894
                                                                     in
                                                                    uu____5891.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____5890
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____5928
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____5928
                                                                    with
                                                                    | 
                                                                    (bs1,c3)
                                                                    ->
                                                                    let bs_subst
                                                                    =
                                                                    let uu____5938
                                                                    =
                                                                    let uu____5945
                                                                    =
                                                                    let uu____5946
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____5946
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____5967
                                                                    =
                                                                    let uu____5970
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5970
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____5945,
                                                                    uu____5967)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____5938
                                                                     in
                                                                    let c4 =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c3  in
                                                                    let uu____5984
                                                                    =
                                                                    let uu____5985
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c4)  in
                                                                    uu____5985.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5984
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____5990,uu____5991::is4)
                                                                    ->
                                                                    let uu____6033
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is4
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____6033
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1))
                                                                    | 
                                                                    uu____6066
                                                                    ->
                                                                    let uu____6067
                                                                    =
                                                                    let uu____6069
                                                                    =
                                                                    let uu____6071
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____6071
                                                                    " is not a repr type"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "Type of g in bind_t:"
                                                                    uu____6069
                                                                     in
                                                                    failwith
                                                                    uu____6067))
                                                                    | 
                                                                    uu____6077
                                                                    ->
                                                                    let uu____6078
                                                                    =
                                                                    let uu____6080
                                                                    =
                                                                    let uu____6082
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____6082
                                                                    " is not a arrow type"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "Type of g in bind_t:"
                                                                    uu____6080
                                                                     in
                                                                    failwith
                                                                    uu____6078
                                                                     in
                                                                    let g =
                                                                    let uu____6089
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
                                                                    let uu____6097
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env i1
                                                                    f_i1  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____6097)
                                                                    uu____6089
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
                                                                    let uu____6106
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env i1
                                                                    g_i1  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g1
                                                                    uu____6106)
                                                                    g is2
                                                                    g_sort_is
                                                                     in
                                                                    let uu____6107
                                                                    =
                                                                    let uu____6108
                                                                    =
                                                                    let uu____6109
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
                                                                    uu____6109;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    uu____6108
                                                                     in
                                                                    let uu____6128
                                                                    =
                                                                    let uu____6129
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_c1 g_c2
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g1
                                                                    uu____6129
                                                                     in
                                                                    (uu____6107,
                                                                    uu____6128))))))))))
                                         in
                                      let mk_bind c11 b1 c21 =
                                        let uu____6154 =
                                          lift_and_destruct env c11 c21  in
                                        match uu____6154 with
                                        | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2))
                                            ->
                                            let bs =
                                              match b1 with
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____6211 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      t1
                                                     in
                                                  [uu____6211]
                                              | FStar_Pervasives_Native.Some
                                                  x ->
                                                  let uu____6231 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____6231]
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
                                                   (FStar_Const.Const_range
                                                      r1))
                                                FStar_Pervasives_Native.None
                                                r1
                                               in
                                            let wp_args =
                                              let uu____6278 =
                                                FStar_Syntax_Syntax.as_arg
                                                  r11
                                                 in
                                              let uu____6287 =
                                                let uu____6298 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1
                                                   in
                                                let uu____6307 =
                                                  let uu____6318 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      t2
                                                     in
                                                  let uu____6327 =
                                                    let uu____6338 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        wp1
                                                       in
                                                    let uu____6347 =
                                                      let uu____6358 =
                                                        let uu____6367 =
                                                          mk_lam wp2  in
                                                        FStar_Syntax_Syntax.as_arg
                                                          uu____6367
                                                         in
                                                      [uu____6358]  in
                                                    uu____6338 :: uu____6347
                                                     in
                                                  uu____6318 :: uu____6327
                                                   in
                                                uu____6298 :: uu____6307  in
                                              uu____6278 :: uu____6287  in
                                            let wp =
                                              let uu____6419 =
                                                let uu____6424 =
                                                  FStar_TypeChecker_Env.inst_effect_fun_with
                                                    [u_t1; u_t2] env md
                                                    md.FStar_Syntax_Syntax.bind_wp
                                                   in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____6424 wp_args
                                                 in
                                              uu____6419
                                                FStar_Pervasives_Native.None
                                                t2.FStar_Syntax_Syntax.pos
                                               in
                                            let uu____6425 =
                                              mk_comp md u_t2 t2 wp
                                                bind_flags
                                               in
                                            let uu____6426 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g_c1 g_c2
                                               in
                                            (uu____6425, uu____6426)
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
                                        let uu____6453 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____6453 with
                                        | (m,uu____6465,lift2) ->
                                            let c23 =
                                              let uu____6468 =
                                                lift_comp c22 m lift2  in
                                              FStar_Syntax_Syntax.mk_Comp
                                                uu____6468
                                               in
                                            let uu____6469 =
                                              destruct_comp c12  in
                                            (match uu____6469 with
                                             | (u1,t1,wp1) ->
                                                 let md_pure_or_ghost =
                                                   FStar_TypeChecker_Env.get_effect_decl
                                                     env
                                                     c12.FStar_Syntax_Syntax.effect_name
                                                    in
                                                 let vc1 =
                                                   let uu____6487 =
                                                     let uu____6492 =
                                                       let uu____6493 =
                                                         FStar_All.pipe_right
                                                           md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                                           FStar_Util.must
                                                          in
                                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                                         [u1] env
                                                         md_pure_or_ghost
                                                         uu____6493
                                                        in
                                                     let uu____6496 =
                                                       let uu____6497 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           t1
                                                          in
                                                       let uu____6506 =
                                                         let uu____6517 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             wp1
                                                            in
                                                         [uu____6517]  in
                                                       uu____6497 ::
                                                         uu____6506
                                                        in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       uu____6492 uu____6496
                                                      in
                                                   uu____6487
                                                     FStar_Pervasives_Native.None
                                                     r1
                                                    in
                                                 let uu____6550 =
                                                   strengthen_comp env
                                                     FStar_Pervasives_Native.None
                                                     c23 vc1 bind_flags
                                                    in
                                                 let uu____6555 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 g_c2
                                                    in
                                                 (uu____6550, uu____6555))
                                         in
                                      let c1_typ =
                                        FStar_TypeChecker_Env.unfold_effect_abbrev
                                          env c1
                                         in
                                      let uu____6557 = destruct_comp c1_typ
                                         in
                                      match uu____6557 with
                                      | (u_res_t1,res_t1,uu____6570) ->
                                          let uu____6571 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____6571
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____6580 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____6580
                                             then
                                               (debug1
                                                  (fun uu____6594  ->
                                                     let uu____6595 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____6597 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____6595 uu____6597);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 mk_bind c1 b c21))
                                             else
                                               (let uu____6605 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____6608 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____6608)
                                                   in
                                                if uu____6605
                                                then
                                                  let e1' =
                                                    let uu____6633 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____6633
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug1
                                                     (fun uu____6645  ->
                                                        let uu____6646 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____6648 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____6646
                                                          uu____6648);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug1
                                                     (fun uu____6663  ->
                                                        let uu____6664 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____6666 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____6664
                                                          uu____6666);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____6673 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____6673
                                                       in
                                                    let c22 =
                                                      weaken_comp env c21
                                                        x_eq_e
                                                       in
                                                    mk_bind c1 b c22))))
                                          else mk_bind c1 b c2))))))
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
      | uu____6691 -> g2
  
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
            (let uu____6715 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____6715)
           in
        let flags =
          if should_return1
          then
            let uu____6723 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____6723
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____6741 =
          let uu____6742 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____6742 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____6755 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____6755
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____6763 =
                  let uu____6765 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____6765  in
                (if uu____6763
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___820_6774 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___820_6774.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___820_6774.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___820_6774.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____6775 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____6775, g_c)
                 else
                   (let uu____6778 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____6778, g_c)))
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
                   let uu____6789 =
                     let uu____6790 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____6790
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____6789
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____6793 =
                   let uu____6798 =
                     let uu____6799 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____6799
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____6798  in
                 match uu____6793 with
                 | (bind_c,g_bind) ->
                     let uu____6808 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____6809 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____6808, uu____6809))
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
            fun uu____6845  ->
              match uu____6845 with
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
                    let uu____6857 =
                      ((let uu____6861 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____6861) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____6857
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6879 =
        let uu____6880 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6880  in
      FStar_Syntax_Syntax.fvar uu____6879 FStar_Syntax_Syntax.delta_constant
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
               fun uu____6950  ->
                 match uu____6950 with
                 | (uu____6964,eff_label,uu____6966,uu____6967) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____6980 =
          let uu____6988 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____7026  ->
                    match uu____7026 with
                    | (uu____7041,uu____7042,flags,uu____7044) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_7061  ->
                                match uu___5_7061 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____7064 -> false))))
             in
          if uu____6988
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____6980 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____7101 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____7103 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____7103
              then
                let uu____7110 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                   in
                (uu____7110, FStar_TypeChecker_Env.trivial_guard)
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____7149 =
                     FStar_Syntax_Util.get_match_with_close_wps
                       md.FStar_Syntax_Syntax.match_wps
                      in
                   match uu____7149 with
                   | (if_then_else1,uu____7159,uu____7160) ->
                       let uu____7161 =
                         FStar_Range.union_ranges
                           wp_t.FStar_Syntax_Syntax.pos
                           wp_e.FStar_Syntax_Syntax.pos
                          in
                       let uu____7162 =
                         let uu____7167 =
                           FStar_TypeChecker_Env.inst_effect_fun_with
                             [u_res_t] env md if_then_else1
                            in
                         let uu____7168 =
                           let uu____7169 = FStar_Syntax_Syntax.as_arg res_t1
                              in
                           let uu____7178 =
                             let uu____7189 = FStar_Syntax_Syntax.as_arg g
                                in
                             let uu____7198 =
                               let uu____7209 =
                                 FStar_Syntax_Syntax.as_arg wp_t  in
                               let uu____7218 =
                                 let uu____7229 =
                                   FStar_Syntax_Syntax.as_arg wp_e  in
                                 [uu____7229]  in
                               uu____7209 :: uu____7218  in
                             uu____7189 :: uu____7198  in
                           uu____7169 :: uu____7178  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____7167 uu____7168
                          in
                       uu____7162 FStar_Pervasives_Native.None uu____7161
                    in
                 let default_case =
                   let post_k =
                     let uu____7282 =
                       let uu____7291 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____7291]  in
                     let uu____7310 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7282 uu____7310  in
                   let kwp =
                     let uu____7316 =
                       let uu____7325 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____7325]  in
                     let uu____7344 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7316 uu____7344  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____7351 =
                       let uu____7352 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____7352]  in
                     let uu____7371 =
                       let uu____7374 =
                         let uu____7381 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____7381
                          in
                       let uu____7382 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____7374 uu____7382  in
                     FStar_Syntax_Util.abs uu____7351 uu____7371
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
                   let uu____7406 =
                     should_not_inline_whole_match ||
                       (let uu____7409 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____7409)
                      in
                   if uu____7406 then cthen true else cthen false  in
                 let uu____7416 =
                   FStar_List.fold_right
                     (fun uu____7462  ->
                        fun uu____7463  ->
                          match (uu____7462, uu____7463) with
                          | ((g,eff_label,uu____7505,cthen),(celse,g_comp))
                              ->
                              let uu____7539 =
                                let uu____7544 = maybe_return eff_label cthen
                                   in
                                FStar_TypeChecker_Common.lcomp_comp
                                  uu____7544
                                 in
                              (match uu____7539 with
                               | (cthen1,gthen) ->
                                   let uu____7551 =
                                     lift_and_destruct env cthen1 celse  in
                                   (match uu____7551 with
                                    | ((md,uu____7581,uu____7582),(uu____7583,uu____7584,wp_then),
                                       (uu____7586,uu____7587,wp_else)) ->
                                        let uu____7607 =
                                          let uu____7608 =
                                            ifthenelse md res_t g wp_then
                                              wp_else
                                             in
                                          mk_comp md u_res_t res_t uu____7608
                                            []
                                           in
                                        let uu____7609 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_comp gthen
                                           in
                                        (uu____7607, uu____7609)))) lcases
                     (default_case, FStar_TypeChecker_Env.trivial_guard)
                    in
                 match uu____7416 with
                 | (comp,g_comp) ->
                     (match lcases with
                      | [] -> (comp, g_comp)
                      | uu____7634::[] -> (comp, g_comp)
                      | uu____7677 ->
                          let comp1 =
                            FStar_TypeChecker_Env.comp_to_comp_typ env comp
                             in
                          let md =
                            FStar_TypeChecker_Env.get_effect_decl env
                              comp1.FStar_Syntax_Syntax.effect_name
                             in
                          let uu____7696 = destruct_comp comp1  in
                          (match uu____7696 with
                           | (uu____7707,uu____7708,wp) ->
                               let uu____7710 =
                                 FStar_Syntax_Util.get_match_with_close_wps
                                   md.FStar_Syntax_Syntax.match_wps
                                  in
                               (match uu____7710 with
                                | (uu____7721,ite_wp,uu____7723) ->
                                    let wp1 =
                                      let uu____7727 =
                                        let uu____7732 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [u_res_t] env md ite_wp
                                           in
                                        let uu____7733 =
                                          let uu____7734 =
                                            FStar_Syntax_Syntax.as_arg res_t
                                             in
                                          let uu____7743 =
                                            let uu____7754 =
                                              FStar_Syntax_Syntax.as_arg wp
                                               in
                                            [uu____7754]  in
                                          uu____7734 :: uu____7743  in
                                        FStar_Syntax_Syntax.mk_Tm_app
                                          uu____7732 uu____7733
                                         in
                                      uu____7727 FStar_Pervasives_Native.None
                                        wp.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____7787 =
                                      mk_comp md u_res_t res_t wp1
                                        bind_cases_flags
                                       in
                                    (uu____7787, g_comp)))))
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
          let uu____7821 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____7821 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____7837 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____7843 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____7837 uu____7843
              else
                (let uu____7852 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____7858 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____7852 uu____7858)
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
          let uu____7883 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____7883
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____7886 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____7886
        then u_res
        else
          (let is_total =
             let uu____7893 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____7893
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____7904 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____7904 with
              | FStar_Pervasives_Native.None  ->
                  let uu____7907 =
                    let uu____7913 =
                      let uu____7915 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____7915
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____7913)
                     in
                  FStar_Errors.raise_error uu____7907
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
      let uu____7939 = destruct_comp ct  in
      match uu____7939 with
      | (u_t,t,wp) ->
          let vc =
            let uu____7958 = FStar_TypeChecker_Env.get_range env  in
            let uu____7959 =
              let uu____7964 =
                let uu____7965 =
                  FStar_All.pipe_right md.FStar_Syntax_Syntax.trivial
                    FStar_Util.must
                   in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____7965
                 in
              let uu____7968 =
                let uu____7969 = FStar_Syntax_Syntax.as_arg t  in
                let uu____7978 =
                  let uu____7989 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____7989]  in
                uu____7969 :: uu____7978  in
              FStar_Syntax_Syntax.mk_Tm_app uu____7964 uu____7968  in
            uu____7959 FStar_Pervasives_Native.None uu____7958  in
          let uu____8022 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____8022)
  
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
               let uu____8063 =
                 let uu____8064 = FStar_Syntax_Subst.compress t2  in
                 uu____8064.FStar_Syntax_Syntax.n  in
               match uu____8063 with
               | FStar_Syntax_Syntax.Tm_type uu____8068 -> true
               | uu____8070 -> false  in
             let uu____8072 =
               let uu____8073 =
                 FStar_Syntax_Util.unrefine
                   lc.FStar_TypeChecker_Common.res_typ
                  in
               uu____8073.FStar_Syntax_Syntax.n  in
             match uu____8072 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____8081 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____8091 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____8091
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____8094 =
                     let uu____8095 =
                       let uu____8096 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____8096
                        in
                     (FStar_Pervasives_Native.None, uu____8095)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____8094
                    in
                 let e1 =
                   let uu____8102 =
                     let uu____8107 =
                       let uu____8108 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____8108]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____8107  in
                   uu____8102 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____8133 -> (e, lc))
  
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
          (let uu____8168 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____8168
           then
             let uu____8171 = FStar_Syntax_Print.term_to_string e  in
             let uu____8173 = FStar_TypeChecker_Common.lcomp_to_string lc  in
             let uu____8175 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____8171 uu____8173 uu____8175
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____8185 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____8185 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____8210 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____8236 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____8236, false)
             else
               (let uu____8246 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____8246, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____8259) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____8271 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____8271
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1003_8287 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1003_8287.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1003_8287.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1003_8287.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____8294 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____8294 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____8310 =
                      let uu____8311 = FStar_TypeChecker_Common.lcomp_comp lc
                         in
                      match uu____8311 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____8331 =
                            let uu____8333 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____8333 = FStar_Syntax_Util.Equal  in
                          if uu____8331
                          then
                            ((let uu____8340 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____8340
                              then
                                let uu____8344 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____8346 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____8344 uu____8346
                              else ());
                             (let uu____8351 = set_result_typ1 c  in
                              (uu____8351, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____8358 ->
                                   true
                               | uu____8366 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____8375 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____8375
                                  in
                               let lc1 =
                                 let uu____8377 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____8378 =
                                   let uu____8379 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____8379)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____8377 uu____8378
                                  in
                               ((let uu____8383 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____8383
                                 then
                                   let uu____8387 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____8389 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____8391 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____8393 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____8387 uu____8389 uu____8391
                                     uu____8393
                                 else ());
                                (let uu____8398 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____8398 with
                                 | (c1,g_lc) ->
                                     let uu____8409 = set_result_typ1 c1  in
                                     let uu____8410 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____8409, uu____8410)))
                             else
                               ((let uu____8414 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____8414
                                 then
                                   let uu____8418 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____8420 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____8418 uu____8420
                                 else ());
                                (let uu____8425 = set_result_typ1 c  in
                                 (uu____8425, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1040_8429 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1040_8429.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1040_8429.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1040_8429.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____8439 =
                      let uu____8440 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____8440
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____8450 =
                           let uu____8451 = FStar_Syntax_Subst.compress f1
                              in
                           uu____8451.FStar_Syntax_Syntax.n  in
                         match uu____8450 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____8458,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____8460;
                                           FStar_Syntax_Syntax.vars =
                                             uu____8461;_},uu____8462)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1056_8488 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1056_8488.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1056_8488.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1056_8488.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____8489 ->
                             let uu____8490 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____8490 with
                              | (c,g_c) ->
                                  ((let uu____8502 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____8502
                                    then
                                      let uu____8506 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____8508 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____8510 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____8512 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____8506 uu____8508 uu____8510
                                        uu____8512
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
                                        let uu____8525 =
                                          let uu____8530 =
                                            let uu____8531 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____8531]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____8530
                                           in
                                        uu____8525
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____8558 =
                                      let uu____8563 =
                                        FStar_All.pipe_left
                                          (fun _8584  ->
                                             FStar_Pervasives_Native.Some
                                               _8584)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____8585 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____8586 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____8587 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____8563
                                        uu____8585 e uu____8586 uu____8587
                                       in
                                    match uu____8558 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1074_8595 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1074_8595.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1074_8595.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____8597 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____8597
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____8600 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____8600 with
                                         | (c2,g_lc) ->
                                             ((let uu____8612 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____8612
                                               then
                                                 let uu____8616 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____8616
                                               else ());
                                              (let uu____8621 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____8621))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_8630  ->
                              match uu___6_8630 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____8633 -> []))
                       in
                    let lc1 =
                      let uu____8635 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____8635 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1090_8637 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1090_8637.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1090_8637.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1090_8637.FStar_TypeChecker_Common.implicits)
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
        let uu____8673 =
          let uu____8676 =
            let uu____8681 =
              let uu____8682 =
                let uu____8691 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____8691  in
              [uu____8682]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____8681  in
          uu____8676 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____8673  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____8714 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____8714
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____8733 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____8749 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____8766 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____8766
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____8782)::(ens,uu____8784)::uu____8785 ->
                    let uu____8828 =
                      let uu____8831 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____8831  in
                    let uu____8832 =
                      let uu____8833 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____8833  in
                    (uu____8828, uu____8832)
                | uu____8836 ->
                    let uu____8847 =
                      let uu____8853 =
                        let uu____8855 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____8855
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____8853)
                       in
                    FStar_Errors.raise_error uu____8847
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____8875)::uu____8876 ->
                    let uu____8903 =
                      let uu____8908 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____8908
                       in
                    (match uu____8903 with
                     | (us_r,uu____8940) ->
                         let uu____8941 =
                           let uu____8946 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____8946
                            in
                         (match uu____8941 with
                          | (us_e,uu____8978) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____8981 =
                                  let uu____8982 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8982
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8981
                                  us_r
                                 in
                              let as_ens =
                                let uu____8984 =
                                  let uu____8985 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8985
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8984
                                  us_e
                                 in
                              let req =
                                let uu____8989 =
                                  let uu____8994 =
                                    let uu____8995 =
                                      let uu____9006 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____9006]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8995
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____8994
                                   in
                                uu____8989 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____9046 =
                                  let uu____9051 =
                                    let uu____9052 =
                                      let uu____9063 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____9063]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____9052
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____9051
                                   in
                                uu____9046 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____9100 =
                                let uu____9103 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____9103  in
                              let uu____9104 =
                                let uu____9105 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____9105  in
                              (uu____9100, uu____9104)))
                | uu____9108 -> failwith "Impossible"))
  
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
      (let uu____9142 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____9142
       then
         let uu____9147 = FStar_Syntax_Print.term_to_string tm  in
         let uu____9149 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____9147 uu____9149
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
        (let uu____9203 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____9203
         then
           let uu____9208 = FStar_Syntax_Print.term_to_string tm  in
           let uu____9210 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____9208
             uu____9210
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____9221 =
      let uu____9223 =
        let uu____9224 = FStar_Syntax_Subst.compress t  in
        uu____9224.FStar_Syntax_Syntax.n  in
      match uu____9223 with
      | FStar_Syntax_Syntax.Tm_app uu____9228 -> false
      | uu____9246 -> true  in
    if uu____9221
    then t
    else
      (let uu____9251 = FStar_Syntax_Util.head_and_args t  in
       match uu____9251 with
       | (head1,args) ->
           let uu____9294 =
             let uu____9296 =
               let uu____9297 = FStar_Syntax_Subst.compress head1  in
               uu____9297.FStar_Syntax_Syntax.n  in
             match uu____9296 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____9302 -> false  in
           if uu____9294
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____9334 ->
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
          ((let uu____9381 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____9381
            then
              let uu____9384 = FStar_Syntax_Print.term_to_string e  in
              let uu____9386 = FStar_Syntax_Print.term_to_string t  in
              let uu____9388 =
                let uu____9390 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____9390
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____9384 uu____9386 uu____9388
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____9403 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____9403 with
              | (formals,uu____9419) ->
                  let n_implicits =
                    let uu____9441 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____9519  ->
                              match uu____9519 with
                              | (uu____9527,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____9534 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____9534 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____9441 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____9659 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____9659 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____9673 =
                      let uu____9679 =
                        let uu____9681 = FStar_Util.string_of_int n_expected
                           in
                        let uu____9683 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____9685 = FStar_Util.string_of_int n_available
                           in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____9681 uu____9683 uu____9685
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____9679)
                       in
                    let uu____9689 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____9673 uu____9689
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_9707 =
              match uu___7_9707 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____9750 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____9750 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _9881,uu____9868) when
                           _9881 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____9914,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Implicit
                                      uu____9916))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____9950 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____9950 with
                            | (v1,uu____9991,g) ->
                                ((let uu____10006 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____10006
                                  then
                                    let uu____10009 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____10009
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____10019 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____10019 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____10112 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____10112))))
                       | (uu____10139,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____10176 =
                             let uu____10189 =
                               let uu____10196 =
                                 let uu____10201 = FStar_Dyn.mkdyn env  in
                                 (uu____10201, tau)  in
                               FStar_Pervasives_Native.Some uu____10196  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____10189
                              in
                           (match uu____10176 with
                            | (v1,uu____10234,g) ->
                                ((let uu____10249 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____10249
                                  then
                                    let uu____10252 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____10252
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____10262 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____10262 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____10355 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____10355))))
                       | (uu____10382,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____10430 =
                       let uu____10457 = inst_n_binders t1  in
                       aux [] uu____10457 bs1  in
                     (match uu____10430 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____10529) -> (e, torig, guard)
                           | (uu____10560,[]) when
                               let uu____10591 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____10591 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____10593 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____10621 ->
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
            | uu____10634 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____10646 =
      let uu____10650 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____10650
        (FStar_List.map
           (fun u  ->
              let uu____10662 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____10662 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____10646 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____10690 = FStar_Util.set_is_empty x  in
      if uu____10690
      then []
      else
        (let s =
           let uu____10708 =
             let uu____10711 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____10711  in
           FStar_All.pipe_right uu____10708 FStar_Util.set_elements  in
         (let uu____10727 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____10727
          then
            let uu____10732 =
              let uu____10734 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____10734  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____10732
          else ());
         (let r =
            let uu____10743 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____10743  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____10782 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____10782
                     then
                       let uu____10787 =
                         let uu____10789 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____10789
                          in
                       let uu____10793 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____10795 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____10787 uu____10793 uu____10795
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
        let uu____10825 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____10825 FStar_Util.set_elements  in
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
        | ([],uu____10864) -> generalized_univ_names
        | (uu____10871,[]) -> explicit_univ_names
        | uu____10878 ->
            let uu____10887 =
              let uu____10893 =
                let uu____10895 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____10895
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____10893)
               in
            FStar_Errors.raise_error uu____10887 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____10917 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____10917
       then
         let uu____10922 = FStar_Syntax_Print.term_to_string t  in
         let uu____10924 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____10922 uu____10924
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____10933 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____10933
        then
          let uu____10938 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____10938
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____10947 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____10947
         then
           let uu____10952 = FStar_Syntax_Print.term_to_string t  in
           let uu____10954 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____10952 uu____10954
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
        let uu____11038 =
          let uu____11040 =
            FStar_Util.for_all
              (fun uu____11054  ->
                 match uu____11054 with
                 | (uu____11064,uu____11065,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____11040  in
        if uu____11038
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____11117 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____11117
              then
                let uu____11120 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____11120
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____11127 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____11127
               then
                 let uu____11130 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____11130
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____11148 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____11148 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____11182 =
             match uu____11182 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____11219 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____11219
                   then
                     let uu____11224 =
                       let uu____11226 =
                         let uu____11230 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____11230
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____11226
                         (FStar_String.concat ", ")
                        in
                     let uu____11278 =
                       let uu____11280 =
                         let uu____11284 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____11284
                           (FStar_List.map
                              (fun u  ->
                                 let uu____11297 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____11299 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____11297
                                   uu____11299))
                          in
                       FStar_All.pipe_right uu____11280
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____11224
                       uu____11278
                   else ());
                  (let univs2 =
                     let uu____11313 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____11325 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____11325) univs1
                       uu____11313
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____11332 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____11332
                    then
                      let uu____11337 =
                        let uu____11339 =
                          let uu____11343 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____11343
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____11339
                          (FStar_String.concat ", ")
                         in
                      let uu____11391 =
                        let uu____11393 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____11407 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____11409 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____11407
                                    uu____11409))
                           in
                        FStar_All.pipe_right uu____11393
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____11337 uu____11391
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____11430 =
             let uu____11447 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____11447  in
           match uu____11430 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____11537 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____11537
                 then ()
                 else
                   (let uu____11542 = lec_hd  in
                    match uu____11542 with
                    | (lb1,uu____11550,uu____11551) ->
                        let uu____11552 = lec2  in
                        (match uu____11552 with
                         | (lb2,uu____11560,uu____11561) ->
                             let msg =
                               let uu____11564 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____11566 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____11564 uu____11566
                                in
                             let uu____11569 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____11569))
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
                 let uu____11637 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____11637
                 then ()
                 else
                   (let uu____11642 = lec_hd  in
                    match uu____11642 with
                    | (lb1,uu____11650,uu____11651) ->
                        let uu____11652 = lec2  in
                        (match uu____11652 with
                         | (lb2,uu____11660,uu____11661) ->
                             let msg =
                               let uu____11664 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____11666 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____11664 uu____11666
                                in
                             let uu____11669 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____11669))
                  in
               let lecs1 =
                 let uu____11680 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____11733 = univs_and_uvars_of_lec this_lec  in
                        match uu____11733 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____11680 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____11838 = lec_hd  in
                   match uu____11838 with
                   | (lbname,e,c) ->
                       let uu____11848 =
                         let uu____11854 =
                           let uu____11856 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____11858 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____11860 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____11856 uu____11858 uu____11860
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____11854)
                          in
                       let uu____11864 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____11848 uu____11864
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____11883 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____11883 with
                         | FStar_Pervasives_Native.Some uu____11892 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____11900 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____11904 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____11904 with
                              | (bs,kres) ->
                                  ((let uu____11948 =
                                      let uu____11949 =
                                        let uu____11952 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____11952
                                         in
                                      uu____11949.FStar_Syntax_Syntax.n  in
                                    match uu____11948 with
                                    | FStar_Syntax_Syntax.Tm_type uu____11953
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____11957 =
                                          let uu____11959 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____11959  in
                                        if uu____11957
                                        then fail1 kres
                                        else ()
                                    | uu____11964 -> fail1 kres);
                                   (let a =
                                      let uu____11966 =
                                        let uu____11969 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _11972  ->
                                             FStar_Pervasives_Native.Some
                                               _11972) uu____11969
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____11966
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____11980 ->
                                          let uu____11989 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____11989
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
                      (fun uu____12092  ->
                         match uu____12092 with
                         | (lbname,e,c) ->
                             let uu____12138 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____12199 ->
                                   let uu____12212 = (e, c)  in
                                   (match uu____12212 with
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
                                                (fun uu____12252  ->
                                                   match uu____12252 with
                                                   | (x,uu____12258) ->
                                                       let uu____12259 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____12259)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____12277 =
                                                let uu____12279 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____12279
                                                 in
                                              if uu____12277
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
                                          let uu____12288 =
                                            let uu____12289 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____12289.FStar_Syntax_Syntax.n
                                             in
                                          match uu____12288 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____12314 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____12314 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____12325 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____12329 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____12329, gen_tvars))
                                in
                             (match uu____12138 with
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
        (let uu____12476 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____12476
         then
           let uu____12479 =
             let uu____12481 =
               FStar_List.map
                 (fun uu____12496  ->
                    match uu____12496 with
                    | (lb,uu____12505,uu____12506) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____12481 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____12479
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____12532  ->
                match uu____12532 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____12561 = gen env is_rec lecs  in
           match uu____12561 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____12660  ->
                       match uu____12660 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____12722 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____12722
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____12770  ->
                           match uu____12770 with
                           | (l,us,e,c,gvs) ->
                               let uu____12804 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____12806 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____12808 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____12810 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____12812 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____12804 uu____12806 uu____12808
                                 uu____12810 uu____12812))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____12857  ->
                match uu____12857 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____12901 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____12901, t, c, gvs)) univnames_lecs
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
              (let uu____12962 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____12962 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____12968 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _12971  -> FStar_Pervasives_Native.Some _12971)
                     uu____12968)
             in
          let is_var e1 =
            let uu____12979 =
              let uu____12980 = FStar_Syntax_Subst.compress e1  in
              uu____12980.FStar_Syntax_Syntax.n  in
            match uu____12979 with
            | FStar_Syntax_Syntax.Tm_name uu____12984 -> true
            | uu____12986 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1546_13007 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1546_13007.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1546_13007.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____13008 -> e2  in
          let env2 =
            let uu___1549_13010 = env1  in
            let uu____13011 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1549_13010.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1549_13010.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1549_13010.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1549_13010.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1549_13010.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1549_13010.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1549_13010.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1549_13010.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1549_13010.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1549_13010.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1549_13010.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1549_13010.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1549_13010.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1549_13010.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1549_13010.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1549_13010.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1549_13010.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____13011;
              FStar_TypeChecker_Env.is_iface =
                (uu___1549_13010.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1549_13010.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1549_13010.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1549_13010.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1549_13010.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1549_13010.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1549_13010.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1549_13010.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1549_13010.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1549_13010.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1549_13010.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1549_13010.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1549_13010.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1549_13010.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1549_13010.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1549_13010.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1549_13010.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1549_13010.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1549_13010.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1549_13010.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1549_13010.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1549_13010.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1549_13010.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1549_13010.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1549_13010.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1549_13010.FStar_TypeChecker_Env.strict_args_tab)
            }  in
          let uu____13013 = check1 env2 t1 t2  in
          match uu____13013 with
          | FStar_Pervasives_Native.None  ->
              let uu____13020 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____13026 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____13020 uu____13026
          | FStar_Pervasives_Native.Some g ->
              ((let uu____13033 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____13033
                then
                  let uu____13038 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____13038
                else ());
               (let uu____13044 = decorate e t2  in (uu____13044, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____13072 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____13072
         then
           let uu____13075 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____13075
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____13089 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____13089 with
         | (c,g_c) ->
             let uu____13101 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____13101
             then
               let uu____13109 =
                 let uu____13111 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____13111  in
               (uu____13109, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____13119 =
                    let uu____13120 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____13120
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____13119
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____13121 = check_trivial_precondition env c1  in
                match uu____13121 with
                | (ct,vc,g_pre) ->
                    ((let uu____13137 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____13137
                      then
                        let uu____13142 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____13142
                      else ());
                     (let uu____13147 =
                        let uu____13149 =
                          let uu____13150 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____13150  in
                        discharge uu____13149  in
                      let uu____13151 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____13147, uu____13151)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_13185 =
        match uu___8_13185 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____13195)::[] -> f fst1
        | uu____13220 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____13232 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____13232
          (fun _13233  -> FStar_TypeChecker_Common.NonTrivial _13233)
         in
      let op_or_e e =
        let uu____13244 =
          let uu____13245 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____13245  in
        FStar_All.pipe_right uu____13244
          (fun _13248  -> FStar_TypeChecker_Common.NonTrivial _13248)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _13255  -> FStar_TypeChecker_Common.NonTrivial _13255)
         in
      let op_or_t t =
        let uu____13266 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____13266
          (fun _13269  -> FStar_TypeChecker_Common.NonTrivial _13269)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _13276  -> FStar_TypeChecker_Common.NonTrivial _13276)
         in
      let short_op_ite uu___9_13282 =
        match uu___9_13282 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____13292)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____13319)::[] ->
            let uu____13360 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____13360
              (fun _13361  -> FStar_TypeChecker_Common.NonTrivial _13361)
        | uu____13362 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____13374 =
          let uu____13382 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____13382)  in
        let uu____13390 =
          let uu____13400 =
            let uu____13408 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____13408)  in
          let uu____13416 =
            let uu____13426 =
              let uu____13434 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____13434)  in
            let uu____13442 =
              let uu____13452 =
                let uu____13460 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____13460)  in
              let uu____13468 =
                let uu____13478 =
                  let uu____13486 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____13486)  in
                [uu____13478; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____13452 :: uu____13468  in
            uu____13426 :: uu____13442  in
          uu____13400 :: uu____13416  in
        uu____13374 :: uu____13390  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____13548 =
            FStar_Util.find_map table
              (fun uu____13563  ->
                 match uu____13563 with
                 | (x,mk1) ->
                     let uu____13580 = FStar_Ident.lid_equals x lid  in
                     if uu____13580
                     then
                       let uu____13585 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____13585
                     else FStar_Pervasives_Native.None)
             in
          (match uu____13548 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____13589 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____13597 =
      let uu____13598 = FStar_Syntax_Util.un_uinst l  in
      uu____13598.FStar_Syntax_Syntax.n  in
    match uu____13597 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____13603 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____13639)::uu____13640 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____13659 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____13668,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____13669))::uu____13670 -> bs
      | uu____13688 ->
          let uu____13689 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____13689 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____13693 =
                 let uu____13694 = FStar_Syntax_Subst.compress t  in
                 uu____13694.FStar_Syntax_Syntax.n  in
               (match uu____13693 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____13698) ->
                    let uu____13719 =
                      FStar_Util.prefix_until
                        (fun uu___10_13759  ->
                           match uu___10_13759 with
                           | (uu____13767,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____13768)) ->
                               false
                           | uu____13773 -> true) bs'
                       in
                    (match uu____13719 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____13809,uu____13810) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____13882,uu____13883) ->
                         let uu____13956 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____13976  ->
                                   match uu____13976 with
                                   | (x,uu____13985) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____13956
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____14034  ->
                                     match uu____14034 with
                                     | (x,i) ->
                                         let uu____14053 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____14053, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____14064 -> bs))
  
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
            let uu____14093 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____14093
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
          let uu____14124 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____14124
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
        (let uu____14167 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____14167
         then
           ((let uu____14172 = FStar_Ident.text_of_lid lident  in
             d uu____14172);
            (let uu____14174 = FStar_Ident.text_of_lid lident  in
             let uu____14176 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____14174 uu____14176))
         else ());
        (let fv =
           let uu____14182 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____14182
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
         let uu____14194 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1706_14196 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1706_14196.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1706_14196.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1706_14196.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1706_14196.FStar_Syntax_Syntax.sigattrs)
           }), uu____14194))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_14214 =
        match uu___11_14214 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____14217 -> false  in
      let reducibility uu___12_14225 =
        match uu___12_14225 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____14232 -> false  in
      let assumption uu___13_14240 =
        match uu___13_14240 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____14244 -> false  in
      let reification uu___14_14252 =
        match uu___14_14252 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____14255 -> true
        | uu____14257 -> false  in
      let inferred uu___15_14265 =
        match uu___15_14265 with
        | FStar_Syntax_Syntax.Discriminator uu____14267 -> true
        | FStar_Syntax_Syntax.Projector uu____14269 -> true
        | FStar_Syntax_Syntax.RecordType uu____14275 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____14285 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____14298 -> false  in
      let has_eq uu___16_14306 =
        match uu___16_14306 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____14310 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____14389 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____14396 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____14407 =
        let uu____14409 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___17_14415  ->
                  match uu___17_14415 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____14418 -> false))
           in
        FStar_All.pipe_right uu____14409 Prims.op_Negation  in
      if uu____14407
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____14439 =
            let uu____14445 =
              let uu____14447 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____14447 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____14445)  in
          FStar_Errors.raise_error uu____14439 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____14465 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____14473 =
            let uu____14475 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____14475  in
          if uu____14473 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____14485),uu____14486) ->
              ((let uu____14498 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____14498
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____14507 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____14507
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____14518 ->
              let uu____14527 =
                let uu____14529 =
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
                Prims.op_Negation uu____14529  in
              if uu____14527 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____14539 ->
              let uu____14546 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____14546 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____14554 ->
              let uu____14561 =
                let uu____14563 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____14563  in
              if uu____14561 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14573 ->
              let uu____14574 =
                let uu____14576 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____14576  in
              if uu____14574 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14586 ->
              let uu____14587 =
                let uu____14589 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____14589  in
              if uu____14587 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____14599 ->
              let uu____14612 =
                let uu____14614 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____14614  in
              if uu____14612 then err'1 () else ()
          | uu____14624 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let has_erased_for_extraction_attr fv =
        let uu____14647 =
          let uu____14652 =
            FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
          FStar_All.pipe_right uu____14652
            (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
           in
        FStar_All.pipe_right uu____14647
          (fun l_opt  ->
             (FStar_Util.is_some l_opt) &&
               (let uu____14671 = FStar_All.pipe_right l_opt FStar_Util.must
                   in
                FStar_All.pipe_right uu____14671
                  (FStar_List.existsb
                     (fun t1  ->
                        let uu____14689 =
                          let uu____14690 = FStar_Syntax_Subst.compress t1
                             in
                          uu____14690.FStar_Syntax_Syntax.n  in
                        match uu____14689 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            FStar_Ident.lid_equals
                              (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              FStar_Parser_Const.must_erase_for_extraction_attr
                            -> true
                        | uu____14696 -> false))))
         in
      let rec aux_whnf env t1 =
        let uu____14722 =
          let uu____14723 = FStar_Syntax_Subst.compress t1  in
          uu____14723.FStar_Syntax_Syntax.n  in
        match uu____14722 with
        | FStar_Syntax_Syntax.Tm_type uu____14727 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (has_erased_for_extraction_attr fv)
        | FStar_Syntax_Syntax.Tm_arrow uu____14730 ->
            let uu____14745 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____14745 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____14778 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____14778
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____14784;
               FStar_Syntax_Syntax.index = uu____14785;
               FStar_Syntax_Syntax.sort = t2;_},uu____14787)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14796,uu____14797) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____14839::[]) ->
            let uu____14878 =
              let uu____14879 = FStar_Syntax_Util.un_uinst head1  in
              uu____14879.FStar_Syntax_Syntax.n  in
            (match uu____14878 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.erased_lid)
                   || (has_erased_for_extraction_attr fv)
             | uu____14884 -> false)
        | uu____14886 -> false
      
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
        (let uu____14896 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____14896
         then
           let uu____14901 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____14901
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
                  let uu____14962 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____14962 r  in
                let uu____14972 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____14972 with
                | (uu____14981,signature) ->
                    let uu____14983 =
                      let uu____14984 = FStar_Syntax_Subst.compress signature
                         in
                      uu____14984.FStar_Syntax_Syntax.n  in
                    (match uu____14983 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14992) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____15040 =
                                FStar_List.fold_left
                                  (fun uu____15079  ->
                                     fun uu____15080  ->
                                       match (uu____15079, uu____15080) with
                                       | ((is,g,substs),(b,uu____15127)) ->
                                           let uu____15156 =
                                             let uu____15169 =
                                               FStar_Syntax_Subst.subst
                                                 substs
                                                 b.FStar_Syntax_Syntax.sort
                                                in
                                             new_implicit_var "" r env
                                               uu____15169
                                              in
                                           (match uu____15156 with
                                            | (t,uu____15182,g_t) ->
                                                let uu____15196 =
                                                  FStar_TypeChecker_Env.conj_guard
                                                    g g_t
                                                   in
                                                ((FStar_List.append is [t]),
                                                  uu____15196,
                                                  (FStar_List.append substs
                                                     [FStar_Syntax_Syntax.NT
                                                        (b, t)]))))
                                  ([], FStar_TypeChecker_Env.trivial_guard,
                                    [FStar_Syntax_Syntax.NT
                                       ((FStar_Pervasives_Native.fst a),
                                         a_tm)]) bs2
                                 in
                              (match uu____15040 with
                               | (is,g,uu____15217) ->
                                   let repr =
                                     let uu____15227 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts [u]
                                        in
                                     FStar_All.pipe_right uu____15227
                                       FStar_Pervasives_Native.snd
                                      in
                                   let uu____15236 =
                                     let uu____15237 =
                                       let uu____15242 =
                                         FStar_List.map
                                           FStar_Syntax_Syntax.as_arg (a_tm
                                           :: is)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr
                                         uu____15242
                                        in
                                     uu____15237 FStar_Pervasives_Native.None
                                       r
                                      in
                                   (uu____15236, g))
                          | uu____15251 -> fail1 signature)
                     | uu____15252 -> fail1 signature)
  
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
  