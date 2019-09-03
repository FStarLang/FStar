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
  = fun c  -> FStar_Syntax_Util.destruct_comp c 
let (lift_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp_typ ->
      FStar_TypeChecker_Env.mlift ->
        (FStar_Syntax_Syntax.comp_typ * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c  ->
      fun lift  ->
        let uu____1075 =
          let uu____1080 = FStar_All.pipe_right c FStar_Syntax_Syntax.mk_Comp
             in
          FStar_All.pipe_right uu____1080
            (lift.FStar_TypeChecker_Env.mlift_wp env)
           in
        FStar_All.pipe_right uu____1075
          (fun uu____1097  ->
             match uu____1097 with
             | (c1,g) ->
                 let uu____1108 =
                   let uu___169_1109 = FStar_Syntax_Util.comp_to_comp_typ c1
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___169_1109.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (uu___169_1109.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___169_1109.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___169_1109.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags = []
                   }  in
                 (uu____1108, g))
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____1126 =
          let uu____1133 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____1134 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____1133 uu____1134  in
        match uu____1126 with | (m,uu____1136,uu____1137) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____1154 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2)
           in
        if uu____1154
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
          FStar_Syntax_Syntax.typ) * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let c11 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
        let c21 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
        let uu____1203 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____1203 with
        | (m,lift1,lift2) ->
            let uu____1239 = lift_comp env c11 lift1  in
            (match uu____1239 with
             | (m1,g1) ->
                 let uu____1272 = lift_comp env c21 lift2  in
                 (match uu____1272 with
                  | (m2,g2) ->
                      let md = FStar_TypeChecker_Env.get_effect_decl env m
                         in
                      let uu____1306 =
                        FStar_TypeChecker_Env.wp_signature env
                          md.FStar_Syntax_Syntax.mname
                         in
                      (match uu____1306 with
                       | (a,kwp) ->
                           let uu____1339 = destruct_comp m1  in
                           let uu____1346 = destruct_comp m2  in
                           let uu____1353 =
                             FStar_TypeChecker_Env.conj_guard g1 g2  in
                           ((md, a, kwp), uu____1339, uu____1346, uu____1353))))
  
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
            let uu____1432 =
              let uu____1433 =
                let uu____1444 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____1444]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____1433;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____1432
  
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
          let uu____1528 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____1528
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1540 =
      let uu____1541 = FStar_Syntax_Subst.compress t  in
      uu____1541.FStar_Syntax_Syntax.n  in
    match uu____1540 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1545 -> true
    | uu____1561 -> false
  
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
              let uu____1631 =
                let uu____1633 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____1633  in
              if uu____1631
              then f
              else (let uu____1640 = reason1 ()  in label uu____1640 r f)
  
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
            let uu___239_1661 = g  in
            let uu____1662 =
              let uu____1663 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____1663  in
            {
              FStar_TypeChecker_Common.guard_f = uu____1662;
              FStar_TypeChecker_Common.deferred =
                (uu___239_1661.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___239_1661.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___239_1661.FStar_TypeChecker_Common.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____1684 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____1684
        then c
        else
          (let uu____1689 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____1689
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let uu____1730 =
                  FStar_Syntax_Util.get_match_with_close_wps
                    md.FStar_Syntax_Syntax.match_wps
                   in
                match uu____1730 with
                | (uu____1739,uu____1740,close1) ->
                    FStar_List.fold_right
                      (fun x  ->
                         fun wp  ->
                           let bs =
                             let uu____1763 = FStar_Syntax_Syntax.mk_binder x
                                in
                             [uu____1763]  in
                           let us =
                             let uu____1785 =
                               let uu____1788 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               [uu____1788]  in
                             u_res :: uu____1785  in
                           let wp1 =
                             FStar_Syntax_Util.abs bs wp
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None
                                     [FStar_Syntax_Syntax.TOTAL]))
                              in
                           let uu____1794 =
                             let uu____1799 =
                               FStar_TypeChecker_Env.inst_effect_fun_with us
                                 env md close1
                                in
                             let uu____1800 =
                               let uu____1801 =
                                 FStar_Syntax_Syntax.as_arg res_t  in
                               let uu____1810 =
                                 let uu____1821 =
                                   FStar_Syntax_Syntax.as_arg
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let uu____1830 =
                                   let uu____1841 =
                                     FStar_Syntax_Syntax.as_arg wp1  in
                                   [uu____1841]  in
                                 uu____1821 :: uu____1830  in
                               uu____1801 :: uu____1810  in
                             FStar_Syntax_Syntax.mk_Tm_app uu____1799
                               uu____1800
                              in
                           uu____1794 FStar_Pervasives_Native.None
                             wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____1883 = destruct_comp c1  in
              match uu____1883 with
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
                let uu____1923 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____1923
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
              ({ FStar_Syntax_Syntax.ppname = uu____1946;
                 FStar_Syntax_Syntax.index = uu____1947;
                 FStar_Syntax_Syntax.sort =
                   { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____1949;
                     FStar_Syntax_Syntax.vars = uu____1950;_};_},uu____1951)
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
              close_comp env [x] c
          | uu____1959 -> c
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_1971  ->
            match uu___0_1971 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____1974 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____1999 =
            let uu____2002 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____2002 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____1999
            (fun c  ->
               (let uu____2058 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____2058) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____2062 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____2062)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____2073 = FStar_Syntax_Util.head_and_args' e  in
                match uu____2073 with
                | (head1,uu____2090) ->
                    let uu____2111 =
                      let uu____2112 = FStar_Syntax_Util.un_uinst head1  in
                      uu____2112.FStar_Syntax_Syntax.n  in
                    (match uu____2111 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2117 =
                           let uu____2119 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____2119
                            in
                         Prims.op_Negation uu____2117
                     | uu____2120 -> true)))
              &&
              (let uu____2123 = should_not_inline_lc lc  in
               Prims.op_Negation uu____2123)
  
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
            let uu____2151 =
              let uu____2153 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____2153  in
            if uu____2151
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____2160 = FStar_Syntax_Util.is_unit t  in
               if uu____2160
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
                    let uu____2169 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____2169
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____2174 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____2174 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____2184 =
                             let uu____2185 =
                               let uu____2190 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____2191 =
                                 let uu____2192 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____2201 =
                                   let uu____2212 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____2212]  in
                                 uu____2192 :: uu____2201  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____2190
                                 uu____2191
                                in
                             uu____2185 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____2184)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____2246 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____2246
           then
             let uu____2251 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____2253 = FStar_Syntax_Print.term_to_string v1  in
             let uu____2255 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____2251 uu____2253 uu____2255
           else ());
          c
  
let (lift_wp_and_bind_with :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
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
                let uu____2293 =
                  FStar_TypeChecker_Env.monad_leq env
                    FStar_Parser_Const.effect_PURE_lid
                    md.FStar_Syntax_Syntax.mname
                   in
                match uu____2293 with
                | FStar_Pervasives_Native.Some edge -> edge
                | FStar_Pervasives_Native.None  ->
                    failwith
                      (Prims.op_Hat
                         "Impossible! lift_wp_and_bind_with: did not find a lift from PURE to "
                         (md.FStar_Syntax_Syntax.mname).FStar_Ident.str)
                 in
              let wp11 =
                let c =
                  let uu____2302 =
                    let uu____2303 =
                      let uu____2314 =
                        FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg
                         in
                      [uu____2314]  in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        [FStar_Syntax_Syntax.U_zero];
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        FStar_Syntax_Syntax.t_unit;
                      FStar_Syntax_Syntax.effect_args = uu____2303;
                      FStar_Syntax_Syntax.flags = []
                    }  in
                  FStar_Syntax_Syntax.mk_Comp uu____2302  in
                let uu____2347 =
                  FStar_All.pipe_right c
                    ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                       env)
                   in
                FStar_All.pipe_right uu____2347
                  (fun uu____2366  ->
                     match uu____2366 with
                     | (c1,g) ->
                         let uu____2375 =
                           FStar_All.pipe_right c1
                             FStar_Syntax_Util.comp_to_comp_typ
                            in
                         FStar_All.pipe_right uu____2375
                           (fun ct  ->
                              let uu____2381 =
                                FStar_All.pipe_right
                                  ct.FStar_Syntax_Syntax.effect_args
                                  FStar_List.hd
                                 in
                              FStar_All.pipe_right uu____2381
                                FStar_Pervasives_Native.fst))
                 in
              let uu____2430 =
                let uu____2435 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [FStar_Syntax_Syntax.U_zero; u_res_t] env md
                    md.FStar_Syntax_Syntax.bind_wp
                   in
                let uu____2436 =
                  let uu____2437 =
                    let uu____2446 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_range r))
                        FStar_Pervasives_Native.None r
                       in
                    FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____2446
                     in
                  let uu____2455 =
                    let uu____2466 =
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        FStar_Syntax_Syntax.t_unit
                       in
                    let uu____2483 =
                      let uu____2494 = FStar_Syntax_Syntax.as_arg res_t  in
                      let uu____2503 =
                        let uu____2514 = FStar_Syntax_Syntax.as_arg wp11  in
                        let uu____2523 =
                          let uu____2534 =
                            let uu____2543 =
                              let uu____2544 =
                                let uu____2545 =
                                  FStar_Syntax_Syntax.null_binder
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                [uu____2545]  in
                              FStar_Syntax_Util.abs uu____2544 wp2
                                (FStar_Pervasives_Native.Some
                                   (FStar_Syntax_Util.mk_residual_comp
                                      FStar_Parser_Const.effect_Tot_lid
                                      FStar_Pervasives_Native.None
                                      [FStar_Syntax_Syntax.TOTAL]))
                               in
                            FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                              uu____2543
                             in
                          [uu____2534]  in
                        uu____2514 :: uu____2523  in
                      uu____2494 :: uu____2503  in
                    uu____2466 :: uu____2483  in
                  uu____2437 :: uu____2455  in
                FStar_Syntax_Syntax.mk_Tm_app uu____2435 uu____2436  in
              uu____2430 FStar_Pervasives_Native.None
                wp2.FStar_Syntax_Syntax.pos
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____2634 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_2640  ->
              match uu___1_2640 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____2643 -> false))
       in
    if uu____2634
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_2655  ->
              match uu___2_2655 with
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
        let uu____2675 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____2675
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____2681 = destruct_comp c1  in
           match uu____2681 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let r = FStar_TypeChecker_Env.get_range env  in
               let pure_assume_wp =
                 let uu____2694 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assume_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____2694  in
               let pure_assume_wp1 =
                 let uu____2699 =
                   let uu____2704 =
                     let uu____2705 =
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula
                        in
                     [uu____2705]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____2704
                    in
                 uu____2699 FStar_Pervasives_Native.None r  in
               let w_wp =
                 lift_wp_and_bind_with env pure_assume_wp1 md u_res_t res_t
                   wp
                  in
               let uu____2739 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t w_wp uu____2739)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____2767 =
          let uu____2768 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____2768 with
          | (c,g_c) ->
              let uu____2779 =
                let uu____2780 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                   in
                if uu____2780
                then c
                else
                  (match f with
                   | FStar_TypeChecker_Common.Trivial  -> c
                   | FStar_TypeChecker_Common.NonTrivial f1 ->
                       weaken_comp env c f1)
                 in
              (uu____2779, g_c)
           in
        let uu____2786 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____2786 weaken
  
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
               let uu____2835 = destruct_comp c1  in
               match uu____2835 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let pure_assert_wp =
                     let uu____2847 =
                       FStar_Syntax_Syntax.lid_as_fv
                         FStar_Parser_Const.pure_assert_wp_lid
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____2847  in
                   let pure_assert_wp1 =
                     let uu____2852 =
                       let uu____2857 =
                         let uu____2858 =
                           let uu____2867 = label_opt env reason r f  in
                           FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                             uu____2867
                            in
                         [uu____2858]  in
                       FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp
                         uu____2857
                        in
                     uu____2852 FStar_Pervasives_Native.None r  in
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
            let uu____2938 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____2938
            then (lc, g0)
            else
              (let flags =
                 let uu____2950 =
                   let uu____2958 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____2958
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____2950 with
                 | (maybe_trivial_post,flags) ->
                     let uu____2988 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_2996  ->
                               match uu___3_2996 with
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
                               | uu____2999 -> []))
                        in
                     FStar_List.append flags uu____2988
                  in
               let strengthen uu____3009 =
                 let uu____3010 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____3010 with
                 | (c,g_c) ->
                     let uu____3021 =
                       if env.FStar_TypeChecker_Env.lax
                       then c
                       else
                         (let g01 =
                            FStar_TypeChecker_Rel.simplify_guard env g0  in
                          let uu____3026 =
                            FStar_TypeChecker_Env.guard_form g01  in
                          match uu____3026 with
                          | FStar_TypeChecker_Common.Trivial  -> c
                          | FStar_TypeChecker_Common.NonTrivial f ->
                              ((let uu____3029 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    FStar_Options.Extreme
                                   in
                                if uu____3029
                                then
                                  let uu____3033 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env e_for_debugging_only
                                     in
                                  let uu____3035 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env f
                                     in
                                  FStar_Util.print2
                                    "-------------Strengthening pre-condition of term %s with guard %s\n"
                                    uu____3033 uu____3035
                                else ());
                               strengthen_comp env reason c f flags))
                        in
                     (uu____3021, g_c)
                  in
               let uu____3040 =
                 let uu____3041 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____3041
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____3040,
                 (let uu___426_3043 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___426_3043.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___426_3043.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___426_3043.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_3052  ->
            match uu___4_3052 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____3056 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____3085 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____3085
          then e
          else
            (let uu____3092 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____3095 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____3095)
                in
             if uu____3092
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
          fun uu____3148  ->
            match uu____3148 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____3168 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____3168 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____3181 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____3181
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____3191 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____3191
                       then
                         let uu____3196 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____3196
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____3203 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____3203
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____3212 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____3212
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____3219 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____3219
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____3235 =
                  let uu____3236 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____3236
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____3244 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____3244, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____3247 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____3247 with
                     | (c1,g_c1) ->
                         let uu____3258 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____3258 with
                          | (c2,g_c2) ->
                              (debug1
                                 (fun uu____3278  ->
                                    let uu____3279 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____3281 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____3286 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____3279 uu____3281 uu____3286);
                               (let aux uu____3304 =
                                  let uu____3305 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____3305
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____3336
                                        ->
                                        let uu____3337 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____3337
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____3369 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____3369
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____3414 =
                                  let uu____3415 =
                                    let uu____3417 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____3417  in
                                  if uu____3415
                                  then
                                    let uu____3431 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____3431
                                     then
                                       FStar_Util.Inl
                                         (c2,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____3454 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____3454))
                                  else
                                    (let uu____3469 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____3469
                                     then
                                       let close1 x reason c =
                                         let x1 =
                                           let uu___496_3511 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___496_3511.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___496_3511.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           }  in
                                         let uu____3512 =
                                           let uu____3518 =
                                             close_comp_if_refinement_t env
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c
                                              in
                                           (uu____3518, reason)  in
                                         FStar_Util.Inl uu____3512  in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some
                                          e,FStar_Pervasives_Native.Some x)
                                           ->
                                           let uu____3554 =
                                             FStar_All.pipe_right c2
                                               (FStar_Syntax_Subst.subst_comp
                                                  [FStar_Syntax_Syntax.NT
                                                     (x, e)])
                                              in
                                           FStar_All.pipe_right uu____3554
                                             (close1 x "c1 Tot")
                                       | (uu____3568,FStar_Pervasives_Native.Some
                                          x) ->
                                           FStar_All.pipe_right c2
                                             (close1 x "c1 Tot only close")
                                       | (uu____3591,uu____3592) -> aux ()
                                     else
                                       (let uu____3607 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____3607
                                        then
                                          let uu____3620 =
                                            let uu____3626 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____3626, "both GTot")  in
                                          FStar_Util.Inl uu____3620
                                        else aux ()))
                                   in
                                let uu____3637 = try_simplify ()  in
                                match uu____3637 with
                                | FStar_Util.Inl (c,reason) ->
                                    (debug1
                                       (fun uu____3667  ->
                                          let uu____3668 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____3668);
                                     (let uu____3671 =
                                        FStar_TypeChecker_Env.conj_guard g_c1
                                          g_c2
                                         in
                                      (c, uu____3671)))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____3683  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_layered_bind c11 b1 c21 =
                                        (let uu____3710 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug env)
                                             (FStar_Options.Other
                                                "LayeredEffects")
                                            in
                                         if uu____3710
                                         then
                                           let uu____3715 =
                                             FStar_Syntax_Print.comp_to_string
                                               c11
                                              in
                                           let uu____3717 =
                                             FStar_Syntax_Print.comp_to_string
                                               c21
                                              in
                                           FStar_Util.print2
                                             "Binding c1:%s and c2:%s {\n"
                                             uu____3715 uu____3717
                                         else ());
                                        (let ct1 =
                                           FStar_TypeChecker_Env.unfold_effect_abbrev
                                             env c11
                                            in
                                         let ct2 =
                                           FStar_TypeChecker_Env.unfold_effect_abbrev
                                             env c21
                                            in
                                         let uu____3724 =
                                           let c1_ed =
                                             FStar_TypeChecker_Env.get_effect_decl
                                               env
                                               ct1.FStar_Syntax_Syntax.effect_name
                                              in
                                           let c2_ed =
                                             FStar_TypeChecker_Env.get_effect_decl
                                               env
                                               ct2.FStar_Syntax_Syntax.effect_name
                                              in
                                           let uu____3735 =
                                             FStar_TypeChecker_Env.monad_leq
                                               env
                                               c1_ed.FStar_Syntax_Syntax.mname
                                               c2_ed.FStar_Syntax_Syntax.mname
                                              in
                                           match uu____3735 with
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____3746 =
                                                 FStar_TypeChecker_Env.monad_leq
                                                   env
                                                   c2_ed.FStar_Syntax_Syntax.mname
                                                   c1_ed.FStar_Syntax_Syntax.mname
                                                  in
                                               (match uu____3746 with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    let uu____3757 =
                                                      let uu____3763 =
                                                        FStar_Util.format2
                                                          "Effects %s and %s cannot be composed"
                                                          (c1_ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                          (c2_ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                         in
                                                      (FStar_Errors.Fatal_EffectsCannotBeComposed,
                                                        uu____3763)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____3757 r1
                                                | FStar_Pervasives_Native.Some
                                                    edge ->
                                                    let uu____3776 =
                                                      let uu____3781 =
                                                        let uu____3786 =
                                                          FStar_All.pipe_right
                                                            ct2
                                                            FStar_Syntax_Syntax.mk_Comp
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____3786
                                                          ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                             env)
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3781
                                                        (fun uu____3803  ->
                                                           match uu____3803
                                                           with
                                                           | (c,g) ->
                                                               let uu____3814
                                                                 =
                                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                                   c
                                                                  in
                                                               (uu____3814,
                                                                 g))
                                                       in
                                                    (match uu____3776 with
                                                     | (ct21,g_lift) ->
                                                         (ct1, ct21, c1_ed,
                                                           g_lift)))
                                           | FStar_Pervasives_Native.Some
                                               edge ->
                                               let uu____3826 =
                                                 let uu____3831 =
                                                   let uu____3836 =
                                                     FStar_All.pipe_right ct1
                                                       FStar_Syntax_Syntax.mk_Comp
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3836
                                                     ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                        env)
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3831
                                                   (fun uu____3853  ->
                                                      match uu____3853 with
                                                      | (c,g) ->
                                                          let uu____3864 =
                                                            FStar_Syntax_Util.comp_to_comp_typ
                                                              c
                                                             in
                                                          (uu____3864, g))
                                                  in
                                               (match uu____3826 with
                                                | (ct11,g_lift) ->
                                                    (ct11, ct2, c2_ed,
                                                      g_lift))
                                            in
                                         match uu____3724 with
                                         | (ct11,ct21,ed,g_lift) ->
                                             ((let uu____3884 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____3884
                                               then
                                                 let uu____3889 =
                                                   let uu____3891 =
                                                     FStar_All.pipe_right
                                                       ct11
                                                       FStar_Syntax_Syntax.mk_Comp
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3891
                                                     FStar_Syntax_Print.comp_to_string
                                                    in
                                                 let uu____3893 =
                                                   let uu____3895 =
                                                     FStar_All.pipe_right
                                                       ct21
                                                       FStar_Syntax_Syntax.mk_Comp
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3895
                                                     FStar_Syntax_Print.comp_to_string
                                                    in
                                                 FStar_Util.print2
                                                   "After lifting, ct1: %s and ct2: %s\n"
                                                   uu____3889 uu____3893
                                               else ());
                                              (let uu____3900 =
                                                 let uu____3911 =
                                                   FStar_List.hd
                                                     ct11.FStar_Syntax_Syntax.comp_univs
                                                    in
                                                 let uu____3912 =
                                                   FStar_List.map
                                                     FStar_Pervasives_Native.fst
                                                     ct11.FStar_Syntax_Syntax.effect_args
                                                    in
                                                 (uu____3911,
                                                   (ct11.FStar_Syntax_Syntax.result_typ),
                                                   uu____3912)
                                                  in
                                               match uu____3900 with
                                               | (u1,t1,is1) ->
                                                   let uu____3946 =
                                                     let uu____3957 =
                                                       FStar_List.hd
                                                         ct21.FStar_Syntax_Syntax.comp_univs
                                                        in
                                                     let uu____3958 =
                                                       FStar_List.map
                                                         FStar_Pervasives_Native.fst
                                                         ct21.FStar_Syntax_Syntax.effect_args
                                                        in
                                                     (uu____3957,
                                                       (ct21.FStar_Syntax_Syntax.result_typ),
                                                       uu____3958)
                                                      in
                                                   (match uu____3946 with
                                                    | (u2,t2,is2) ->
                                                        let uu____3992 =
                                                          FStar_TypeChecker_Env.inst_tscheme_with
                                                            ed.FStar_Syntax_Syntax.bind_wp
                                                            [u1; u2]
                                                           in
                                                        (match uu____3992
                                                         with
                                                         | (uu____4001,bind_t)
                                                             ->
                                                             let bind_t_shape_error
                                                               s =
                                                               let uu____4016
                                                                 =
                                                                 let uu____4018
                                                                   =
                                                                   FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                    in
                                                                 FStar_Util.format2
                                                                   "bind %s does not have proper shape (reason:%s)"
                                                                   uu____4018
                                                                   s
                                                                  in
                                                               (FStar_Errors.Fatal_UnexpectedEffect,
                                                                 uu____4016)
                                                                in
                                                             let uu____4022 =
                                                               let uu____4067
                                                                 =
                                                                 let uu____4068
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    bind_t
                                                                    in
                                                                 uu____4068.FStar_Syntax_Syntax.n
                                                                  in
                                                               match uu____4067
                                                               with
                                                               | FStar_Syntax_Syntax.Tm_arrow
                                                                   (bs,c)
                                                                   when
                                                                   (FStar_List.length
                                                                    bs) >=
                                                                    (Prims.of_int (4))
                                                                   ->
                                                                   let uu____4144
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                   (match uu____4144
                                                                    with
                                                                    | 
                                                                    (a_b::b_b::bs1,c3)
                                                                    ->
                                                                    let uu____4229
                                                                    =
                                                                    let uu____4256
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs1) -
                                                                    (Prims.of_int (2)))
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____4256
                                                                    (fun
                                                                    uu____4341
                                                                     ->
                                                                    match uu____4341
                                                                    with
                                                                    | 
                                                                    (l1,l2)
                                                                    ->
                                                                    let uu____4422
                                                                    =
                                                                    FStar_List.hd
                                                                    l2  in
                                                                    let uu____4435
                                                                    =
                                                                    let uu____4442
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                    FStar_List.hd
                                                                    uu____4442
                                                                     in
                                                                    (l1,
                                                                    uu____4422,
                                                                    uu____4435))
                                                                     in
                                                                    (match uu____4229
                                                                    with
                                                                    | 
                                                                    (rest_bs,f_b,g_b)
                                                                    ->
                                                                    let uu____4570
                                                                    =
                                                                    FStar_Syntax_Util.comp_to_comp_typ
                                                                    c3  in
                                                                    (a_b,
                                                                    b_b,
                                                                    rest_bs,
                                                                    f_b, g_b,
                                                                    uu____4570)))
                                                               | uu____4603
                                                                   ->
                                                                   let uu____4604
                                                                    =
                                                                    bind_t_shape_error
                                                                    "Either not an arrow or not enough binders"
                                                                     in
                                                                   FStar_Errors.raise_error
                                                                    uu____4604
                                                                    r1
                                                                in
                                                             (match uu____4022
                                                              with
                                                              | (a_b,b_b,rest_bs,f_b,g_b,bind_ct)
                                                                  ->
                                                                  let uu____4729
                                                                    =
                                                                    let uu____4736
                                                                    =
                                                                    let uu____4737
                                                                    =
                                                                    let uu____4738
                                                                    =
                                                                    let uu____4745
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    a_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    (uu____4745,
                                                                    t1)  in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4738
                                                                     in
                                                                    let uu____4756
                                                                    =
                                                                    let uu____4759
                                                                    =
                                                                    let uu____4760
                                                                    =
                                                                    let uu____4767
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    b_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    (uu____4767,
                                                                    t2)  in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4760
                                                                     in
                                                                    [uu____4759]
                                                                     in
                                                                    uu____4737
                                                                    ::
                                                                    uu____4756
                                                                     in
                                                                    FStar_TypeChecker_Env.uvars_for_binders
                                                                    env
                                                                    rest_bs
                                                                    uu____4736
                                                                    (fun b2 
                                                                    ->
                                                                    let uu____4782
                                                                    =
                                                                    FStar_Syntax_Print.binder_to_string
                                                                    b2  in
                                                                    let uu____4784
                                                                    =
                                                                    FStar_Range.string_of_range
                                                                    r1  in
                                                                    FStar_Util.format3
                                                                    "implicit var for binder %s of %s:bind at %s"
                                                                    uu____4782
                                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                                    uu____4784)
                                                                    r1  in
                                                                  (match uu____4729
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
                                                                    let uu____4821
                                                                    =
                                                                    let uu____4828
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    b2
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    (uu____4828,
                                                                    t)  in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4821)
                                                                    (a_b ::
                                                                    b_b ::
                                                                    rest_bs)
                                                                    (t1 :: t2
                                                                    ::
                                                                    rest_bs_uvars)
                                                                     in
                                                                    let f_guard
                                                                    =
                                                                    let f_sort_is
                                                                    =
                                                                    let uu____4855
                                                                    =
                                                                    let uu____4856
                                                                    =
                                                                    let uu____4859
                                                                    =
                                                                    let uu____4860
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    f_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    uu____4860.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_Syntax_Subst.compress
                                                                    uu____4859
                                                                     in
                                                                    uu____4856.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____4855
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____4871,uu____4872::is)
                                                                    ->
                                                                    let uu____4914
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4914
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1))
                                                                    | 
                                                                    uu____4947
                                                                    ->
                                                                    let uu____4948
                                                                    =
                                                                    bind_t_shape_error
                                                                    "f's type is not a repr type"
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____4948
                                                                    r1  in
                                                                    FStar_List.fold_left2
                                                                    (fun g 
                                                                    ->
                                                                    fun i1 
                                                                    ->
                                                                    fun f_i1 
                                                                    ->
                                                                    let uu____4964
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env i1
                                                                    f_i1  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____4964)
                                                                    FStar_TypeChecker_Env.trivial_guard
                                                                    is1
                                                                    f_sort_is
                                                                     in
                                                                    let g_guard
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
                                                                    let g_sort_is
                                                                    =
                                                                    let uu____4983
                                                                    =
                                                                    let uu____4984
                                                                    =
                                                                    let uu____4987
                                                                    =
                                                                    let uu____4988
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    g_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    uu____4988.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_Syntax_Subst.compress
                                                                    uu____4987
                                                                     in
                                                                    uu____4984.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____4983
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____5021
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____5021
                                                                    with
                                                                    | 
                                                                    (bs1,c3)
                                                                    ->
                                                                    let bs_subst
                                                                    =
                                                                    let uu____5031
                                                                    =
                                                                    let uu____5038
                                                                    =
                                                                    let uu____5039
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____5039
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____5060
                                                                    =
                                                                    let uu____5063
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5063
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____5038,
                                                                    uu____5060)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____5031
                                                                     in
                                                                    let c4 =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c3  in
                                                                    let uu____5077
                                                                    =
                                                                    let uu____5078
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c4)  in
                                                                    uu____5078.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5077
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____5083,uu____5084::is)
                                                                    ->
                                                                    let uu____5126
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5126
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1))
                                                                    | 
                                                                    uu____5159
                                                                    ->
                                                                    let uu____5160
                                                                    =
                                                                    bind_t_shape_error
                                                                    "g's type is not a repr type"
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____5160
                                                                    r1))
                                                                    | 
                                                                    uu____5169
                                                                    ->
                                                                    let uu____5170
                                                                    =
                                                                    bind_t_shape_error
                                                                    "g's type is not an arrow"
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____5170
                                                                    r1  in
                                                                    let env_g
                                                                    =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env 
                                                                    [x_a]  in
                                                                    let uu____5192
                                                                    =
                                                                    FStar_List.fold_left2
                                                                    (fun g 
                                                                    ->
                                                                    fun i1 
                                                                    ->
                                                                    fun g_i1 
                                                                    ->
                                                                    let uu____5200
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env_g i1
                                                                    g_i1  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____5200)
                                                                    FStar_TypeChecker_Env.trivial_guard
                                                                    is2
                                                                    g_sort_is
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5192
                                                                    (FStar_TypeChecker_Env.close_guard
                                                                    env 
                                                                    [x_a])
                                                                     in
                                                                    let is =
                                                                    let uu____5216
                                                                    =
                                                                    let uu____5217
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    bind_ct.FStar_Syntax_Syntax.result_typ
                                                                     in
                                                                    uu____5217.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____5216
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____5222,uu____5223::is)
                                                                    ->
                                                                    let uu____5265
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5265
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1))
                                                                    | 
                                                                    uu____5298
                                                                    ->
                                                                    let uu____5299
                                                                    =
                                                                    bind_t_shape_error
                                                                    "return type is not a repr type"
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____5299
                                                                    r1  in
                                                                    let c =
                                                                    let uu____5309
                                                                    =
                                                                    let uu____5310
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    is  in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    (ct21.FStar_Syntax_Syntax.comp_univs);
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = t2;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____5310;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    uu____5309
                                                                     in
                                                                    ((
                                                                    let uu____5330
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "LayeredEffects")
                                                                     in
                                                                    if
                                                                    uu____5330
                                                                    then
                                                                    let uu____5335
                                                                    =
                                                                    FStar_Syntax_Print.comp_to_string
                                                                    c  in
                                                                    FStar_Util.print1
                                                                    "} c after bind: %s\n"
                                                                    uu____5335
                                                                    else ());
                                                                    (let uu____5340
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guards
                                                                    [g_c1;
                                                                    g_c2;
                                                                    g_lift;
                                                                    g_uvars;
                                                                    f_guard;
                                                                    g_guard]
                                                                     in
                                                                    (c,
                                                                    uu____5340))))))))))
                                         in
                                      let mk_bind c11 b1 c21 =
                                        let uu____5365 =
                                          lift_and_destruct env c11 c21  in
                                        match uu____5365 with
                                        | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2),g)
                                            ->
                                            let bs =
                                              match b1 with
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____5425 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      t1
                                                     in
                                                  [uu____5425]
                                              | FStar_Pervasives_Native.Some
                                                  x ->
                                                  let uu____5445 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____5445]
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
                                              let uu____5492 =
                                                FStar_Syntax_Syntax.as_arg
                                                  r11
                                                 in
                                              let uu____5501 =
                                                let uu____5512 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1
                                                   in
                                                let uu____5521 =
                                                  let uu____5532 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      t2
                                                     in
                                                  let uu____5541 =
                                                    let uu____5552 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        wp1
                                                       in
                                                    let uu____5561 =
                                                      let uu____5572 =
                                                        let uu____5581 =
                                                          mk_lam wp2  in
                                                        FStar_Syntax_Syntax.as_arg
                                                          uu____5581
                                                         in
                                                      [uu____5572]  in
                                                    uu____5552 :: uu____5561
                                                     in
                                                  uu____5532 :: uu____5541
                                                   in
                                                uu____5512 :: uu____5521  in
                                              uu____5492 :: uu____5501  in
                                            let wp =
                                              let uu____5633 =
                                                let uu____5638 =
                                                  FStar_TypeChecker_Env.inst_effect_fun_with
                                                    [u_t1; u_t2] env md
                                                    md.FStar_Syntax_Syntax.bind_wp
                                                   in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____5638 wp_args
                                                 in
                                              uu____5633
                                                FStar_Pervasives_Native.None
                                                t2.FStar_Syntax_Syntax.pos
                                               in
                                            let uu____5639 =
                                              mk_comp md u_t2 t2 wp
                                                bind_flags
                                               in
                                            let uu____5640 =
                                              let uu____5641 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g_c1 g_c2
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                uu____5641 g
                                               in
                                            (uu____5639, uu____5640)
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
                                        let uu____5668 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____5668 with
                                        | (m,uu____5680,lift2) ->
                                            let uu____5682 =
                                              let uu____5687 =
                                                lift_comp env c22 lift2  in
                                              FStar_All.pipe_right uu____5687
                                                (fun uu____5704  ->
                                                   match uu____5704 with
                                                   | (c,g) ->
                                                       let uu____5715 =
                                                         FStar_Syntax_Syntax.mk_Comp
                                                           c
                                                          in
                                                       (uu____5715, g))
                                               in
                                            (match uu____5682 with
                                             | (c23,g2) ->
                                                 let uu____5722 =
                                                   destruct_comp c12  in
                                                 (match uu____5722 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let vc1 =
                                                        let uu____5740 =
                                                          let uu____5745 =
                                                            let uu____5746 =
                                                              FStar_All.pipe_right
                                                                md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                                                FStar_Util.must
                                                               in
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              uu____5746
                                                             in
                                                          let uu____5749 =
                                                            let uu____5750 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____5759 =
                                                              let uu____5770
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____5770]
                                                               in
                                                            uu____5750 ::
                                                              uu____5759
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____5745
                                                            uu____5749
                                                           in
                                                        uu____5740
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____5803 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      let uu____5808 =
                                                        let uu____5809 =
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g_c1 g_c2
                                                           in
                                                        FStar_TypeChecker_Env.conj_guard
                                                          uu____5809 g2
                                                         in
                                                      (uu____5803,
                                                        uu____5808)))
                                         in
                                      let uu____5810 =
                                        let ct1 =
                                          FStar_TypeChecker_Env.unfold_effect_abbrev
                                            env c1
                                           in
                                        let ct2 =
                                          FStar_TypeChecker_Env.unfold_effect_abbrev
                                            env c2
                                           in
                                        (FStar_TypeChecker_Env.is_layered_effect
                                           env
                                           ct1.FStar_Syntax_Syntax.effect_name)
                                          ||
                                          (FStar_TypeChecker_Env.is_layered_effect
                                             env
                                             ct2.FStar_Syntax_Syntax.effect_name)
                                         in
                                      if uu____5810
                                      then mk_layered_bind c1 b c2
                                      else
                                        (let c1_typ =
                                           FStar_TypeChecker_Env.unfold_effect_abbrev
                                             env c1
                                            in
                                         let uu____5822 =
                                           destruct_comp c1_typ  in
                                         match uu____5822 with
                                         | (u_res_t1,res_t1,uu____5835) ->
                                             let uu____5836 =
                                               (FStar_Option.isSome b) &&
                                                 (should_return env e1opt
                                                    lc11)
                                                in
                                             if uu____5836
                                             then
                                               let e1 =
                                                 FStar_Option.get e1opt  in
                                               let x = FStar_Option.get b  in
                                               let uu____5845 =
                                                 FStar_Syntax_Util.is_partial_return
                                                   c1
                                                  in
                                               (if uu____5845
                                                then
                                                  (debug1
                                                     (fun uu____5859  ->
                                                        let uu____5860 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____5862 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case a): Substituting %s for %s"
                                                          uu____5860
                                                          uu____5862);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    mk_bind c1 b c21))
                                                else
                                                  (let uu____5870 =
                                                     ((FStar_Options.vcgen_optimize_bind_as_seq
                                                         ())
                                                        &&
                                                        (lcomp_has_trivial_postcondition
                                                           lc11))
                                                       &&
                                                       (let uu____5873 =
                                                          FStar_TypeChecker_Env.try_lookup_lid
                                                            env
                                                            FStar_Parser_Const.with_type_lid
                                                           in
                                                        FStar_Option.isSome
                                                          uu____5873)
                                                      in
                                                   if uu____5870
                                                   then
                                                     let e1' =
                                                       let uu____5898 =
                                                         FStar_Options.vcgen_decorate_with_type
                                                           ()
                                                          in
                                                       if uu____5898
                                                       then
                                                         FStar_Syntax_Util.mk_with_type
                                                           u_res_t1 res_t1 e1
                                                       else e1  in
                                                     (debug1
                                                        (fun uu____5910  ->
                                                           let uu____5911 =
                                                             FStar_TypeChecker_Normalize.term_to_string
                                                               env e1'
                                                              in
                                                           let uu____5913 =
                                                             FStar_Syntax_Print.bv_to_string
                                                               x
                                                              in
                                                           FStar_Util.print2
                                                             "(3) bind (case b): Substituting %s for %s"
                                                             uu____5911
                                                             uu____5913);
                                                      (let c21 =
                                                         FStar_Syntax_Subst.subst_comp
                                                           [FStar_Syntax_Syntax.NT
                                                              (x, e1')] c2
                                                          in
                                                       mk_seq c1 b c21))
                                                   else
                                                     (debug1
                                                        (fun uu____5928  ->
                                                           let uu____5929 =
                                                             FStar_TypeChecker_Normalize.term_to_string
                                                               env e1
                                                              in
                                                           let uu____5931 =
                                                             FStar_Syntax_Print.bv_to_string
                                                               x
                                                              in
                                                           FStar_Util.print2
                                                             "(3) bind (case c): Adding equality %s = %s"
                                                             uu____5929
                                                             uu____5931);
                                                      (let c21 =
                                                         FStar_Syntax_Subst.subst_comp
                                                           [FStar_Syntax_Syntax.NT
                                                              (x, e1)] c2
                                                          in
                                                       let x_eq_e =
                                                         let uu____5938 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_Syntax_Util.mk_eq2
                                                           u_res_t1 res_t1 e1
                                                           uu____5938
                                                          in
                                                       let c22 =
                                                         weaken_comp env c21
                                                           x_eq_e
                                                          in
                                                       mk_bind c1 b c22))))
                                             else mk_bind c1 b c2)))))))
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
      | uu____5956 -> g2
  
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
            (let uu____5980 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____5980)
           in
        let flags =
          if should_return1
          then
            let uu____5988 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____5988
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____6006 =
          let uu____6007 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____6007 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____6020 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____6020
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____6028 =
                  let uu____6030 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____6030  in
                (if uu____6028
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___757_6039 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___757_6039.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___757_6039.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___757_6039.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____6040 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____6040, g_c)
                 else
                   (let uu____6043 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____6043, g_c)))
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
                   let uu____6054 =
                     let uu____6055 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____6055
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____6054
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____6058 =
                   let uu____6063 =
                     let uu____6064 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____6064
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____6063  in
                 match uu____6058 with
                 | (bind_c,g_bind) ->
                     let uu____6073 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____6074 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____6073, uu____6074))
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
            fun uu____6110  ->
              match uu____6110 with
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
                    let uu____6122 =
                      ((let uu____6126 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____6126) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____6122
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6144 =
        let uu____6145 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6145  in
      FStar_Syntax_Syntax.fvar uu____6144 FStar_Syntax_Syntax.delta_constant
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
               fun uu____6215  ->
                 match uu____6215 with
                 | (uu____6229,eff_label,uu____6231,uu____6232) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____6245 =
          let uu____6253 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____6291  ->
                    match uu____6291 with
                    | (uu____6306,uu____6307,flags,uu____6309) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_6326  ->
                                match uu___5_6326 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____6329 -> false))))
             in
          if uu____6253
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____6245 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____6366 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____6368 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____6368
              then
                let uu____6375 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                   in
                (uu____6375, FStar_TypeChecker_Env.trivial_guard)
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____6414 =
                     FStar_Syntax_Util.get_match_with_close_wps
                       md.FStar_Syntax_Syntax.match_wps
                      in
                   match uu____6414 with
                   | (if_then_else1,uu____6424,uu____6425) ->
                       let uu____6426 =
                         FStar_Range.union_ranges
                           wp_t.FStar_Syntax_Syntax.pos
                           wp_e.FStar_Syntax_Syntax.pos
                          in
                       let uu____6427 =
                         let uu____6432 =
                           FStar_TypeChecker_Env.inst_effect_fun_with
                             [u_res_t] env md if_then_else1
                            in
                         let uu____6433 =
                           let uu____6434 = FStar_Syntax_Syntax.as_arg res_t1
                              in
                           let uu____6443 =
                             let uu____6454 = FStar_Syntax_Syntax.as_arg g
                                in
                             let uu____6463 =
                               let uu____6474 =
                                 FStar_Syntax_Syntax.as_arg wp_t  in
                               let uu____6483 =
                                 let uu____6494 =
                                   FStar_Syntax_Syntax.as_arg wp_e  in
                                 [uu____6494]  in
                               uu____6474 :: uu____6483  in
                             uu____6454 :: uu____6463  in
                           uu____6434 :: uu____6443  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____6432 uu____6433
                          in
                       uu____6427 FStar_Pervasives_Native.None uu____6426
                    in
                 let default_case =
                   let post_k =
                     let uu____6547 =
                       let uu____6556 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____6556]  in
                     let uu____6575 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6547 uu____6575  in
                   let kwp =
                     let uu____6581 =
                       let uu____6590 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____6590]  in
                     let uu____6609 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6581 uu____6609  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____6616 =
                       let uu____6617 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____6617]  in
                     let uu____6636 =
                       let uu____6639 =
                         let uu____6646 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____6646
                          in
                       let uu____6647 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____6639 uu____6647  in
                     FStar_Syntax_Util.abs uu____6616 uu____6636
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
                   let uu____6671 =
                     should_not_inline_whole_match ||
                       (let uu____6674 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____6674)
                      in
                   if uu____6671 then cthen true else cthen false  in
                 let uu____6681 =
                   FStar_List.fold_right
                     (fun uu____6728  ->
                        fun uu____6729  ->
                          match (uu____6728, uu____6729) with
                          | ((g,eff_label,uu____6771,cthen),(celse,g_comp))
                              ->
                              let uu____6805 =
                                let uu____6810 = maybe_return eff_label cthen
                                   in
                                FStar_TypeChecker_Common.lcomp_comp
                                  uu____6810
                                 in
                              (match uu____6805 with
                               | (cthen1,gthen) ->
                                   let uu____6817 =
                                     lift_and_destruct env cthen1 celse  in
                                   (match uu____6817 with
                                    | ((md,uu____6849,uu____6850),(uu____6851,uu____6852,wp_then),
                                       (uu____6854,uu____6855,wp_else),g_lift)
                                        ->
                                        let uu____6876 =
                                          let uu____6877 =
                                            ifthenelse md res_t g wp_then
                                              wp_else
                                             in
                                          mk_comp md u_res_t res_t uu____6877
                                            []
                                           in
                                        let uu____6878 =
                                          let uu____6879 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_comp gthen
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            uu____6879 g_lift
                                           in
                                        (uu____6876, uu____6878)))) lcases
                     (default_case, FStar_TypeChecker_Env.trivial_guard)
                    in
                 match uu____6681 with
                 | (comp,g_comp) ->
                     (match lcases with
                      | [] -> (comp, g_comp)
                      | uu____6904::[] -> (comp, g_comp)
                      | uu____6947 ->
                          let comp1 =
                            FStar_TypeChecker_Env.comp_to_comp_typ env comp
                             in
                          let md =
                            FStar_TypeChecker_Env.get_effect_decl env
                              comp1.FStar_Syntax_Syntax.effect_name
                             in
                          let uu____6966 = destruct_comp comp1  in
                          (match uu____6966 with
                           | (uu____6977,uu____6978,wp) ->
                               let uu____6980 =
                                 FStar_Syntax_Util.get_match_with_close_wps
                                   md.FStar_Syntax_Syntax.match_wps
                                  in
                               (match uu____6980 with
                                | (uu____6991,ite_wp,uu____6993) ->
                                    let wp1 =
                                      let uu____6997 =
                                        let uu____7002 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [u_res_t] env md ite_wp
                                           in
                                        let uu____7003 =
                                          let uu____7004 =
                                            FStar_Syntax_Syntax.as_arg res_t
                                             in
                                          let uu____7013 =
                                            let uu____7024 =
                                              FStar_Syntax_Syntax.as_arg wp
                                               in
                                            [uu____7024]  in
                                          uu____7004 :: uu____7013  in
                                        FStar_Syntax_Syntax.mk_Tm_app
                                          uu____7002 uu____7003
                                         in
                                      uu____6997 FStar_Pervasives_Native.None
                                        wp.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____7057 =
                                      mk_comp md u_res_t res_t wp1
                                        bind_cases_flags
                                       in
                                    (uu____7057, g_comp)))))
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
          let uu____7091 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____7091 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____7107 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____7113 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____7107 uu____7113
              else
                (let uu____7122 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____7128 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____7122 uu____7128)
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
          let uu____7153 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____7153
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____7156 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____7156
        then u_res
        else
          (let is_total =
             let uu____7163 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____7163
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____7174 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____7174 with
              | FStar_Pervasives_Native.None  ->
                  let uu____7177 =
                    let uu____7183 =
                      let uu____7185 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____7185
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____7183)
                     in
                  FStar_Errors.raise_error uu____7177
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
      let uu____7209 = destruct_comp ct  in
      match uu____7209 with
      | (u_t,t,wp) ->
          let vc =
            let uu____7228 = FStar_TypeChecker_Env.get_range env  in
            let uu____7229 =
              let uu____7234 =
                let uu____7235 =
                  FStar_All.pipe_right md.FStar_Syntax_Syntax.trivial
                    FStar_Util.must
                   in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____7235
                 in
              let uu____7238 =
                let uu____7239 = FStar_Syntax_Syntax.as_arg t  in
                let uu____7248 =
                  let uu____7259 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____7259]  in
                uu____7239 :: uu____7248  in
              FStar_Syntax_Syntax.mk_Tm_app uu____7234 uu____7238  in
            uu____7229 FStar_Pervasives_Native.None uu____7228  in
          let uu____7292 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____7292)
  
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
               let uu____7333 =
                 let uu____7334 = FStar_Syntax_Subst.compress t2  in
                 uu____7334.FStar_Syntax_Syntax.n  in
               match uu____7333 with
               | FStar_Syntax_Syntax.Tm_type uu____7338 -> true
               | uu____7340 -> false  in
             let uu____7342 =
               let uu____7343 =
                 FStar_Syntax_Util.unrefine
                   lc.FStar_TypeChecker_Common.res_typ
                  in
               uu____7343.FStar_Syntax_Syntax.n  in
             match uu____7342 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____7351 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____7361 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____7361
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____7364 =
                     let uu____7365 =
                       let uu____7366 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____7366
                        in
                     (FStar_Pervasives_Native.None, uu____7365)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____7364
                    in
                 let e1 =
                   let uu____7372 =
                     let uu____7377 =
                       let uu____7378 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____7378]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____7377  in
                   uu____7372 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____7403 -> (e, lc))
  
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
          (let uu____7438 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____7438
           then
             let uu____7441 = FStar_Syntax_Print.term_to_string e  in
             let uu____7443 = FStar_TypeChecker_Common.lcomp_to_string lc  in
             let uu____7445 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____7441 uu____7443 uu____7445
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____7455 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____7455 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____7480 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____7506 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____7506, false)
             else
               (let uu____7516 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____7516, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____7529) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____7541 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____7541
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___941_7557 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___941_7557.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___941_7557.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___941_7557.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____7564 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____7564 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____7580 =
                      let uu____7581 = FStar_TypeChecker_Common.lcomp_comp lc
                         in
                      match uu____7581 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____7601 =
                            let uu____7603 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____7603 = FStar_Syntax_Util.Equal  in
                          if uu____7601
                          then
                            ((let uu____7610 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____7610
                              then
                                let uu____7614 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____7616 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____7614 uu____7616
                              else ());
                             (let uu____7621 = set_result_typ1 c  in
                              (uu____7621, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____7628 ->
                                   true
                               | uu____7636 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____7645 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____7645
                                  in
                               let lc1 =
                                 let uu____7647 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____7648 =
                                   let uu____7649 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____7649)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____7647 uu____7648
                                  in
                               ((let uu____7653 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____7653
                                 then
                                   let uu____7657 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____7659 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____7661 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____7663 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____7657 uu____7659 uu____7661
                                     uu____7663
                                 else ());
                                (let uu____7668 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____7668 with
                                 | (c1,g_lc) ->
                                     let uu____7679 = set_result_typ1 c1  in
                                     let uu____7680 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____7679, uu____7680)))
                             else
                               ((let uu____7684 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____7684
                                 then
                                   let uu____7688 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____7690 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____7688 uu____7690
                                 else ());
                                (let uu____7695 = set_result_typ1 c  in
                                 (uu____7695, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___978_7699 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___978_7699.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___978_7699.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___978_7699.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____7709 =
                      let uu____7710 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____7710
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____7720 =
                           let uu____7721 = FStar_Syntax_Subst.compress f1
                              in
                           uu____7721.FStar_Syntax_Syntax.n  in
                         match uu____7720 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____7728,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____7730;
                                           FStar_Syntax_Syntax.vars =
                                             uu____7731;_},uu____7732)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___994_7758 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___994_7758.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___994_7758.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___994_7758.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____7759 ->
                             let uu____7760 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____7760 with
                              | (c,g_c) ->
                                  ((let uu____7772 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____7772
                                    then
                                      let uu____7776 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____7778 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____7780 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____7782 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____7776 uu____7778 uu____7780
                                        uu____7782
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
                                        let uu____7795 =
                                          let uu____7800 =
                                            let uu____7801 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____7801]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____7800
                                           in
                                        uu____7795
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____7828 =
                                      let uu____7833 =
                                        FStar_All.pipe_left
                                          (fun _7854  ->
                                             FStar_Pervasives_Native.Some
                                               _7854)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____7855 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____7856 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____7857 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____7833
                                        uu____7855 e uu____7856 uu____7857
                                       in
                                    match uu____7828 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1012_7865 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1012_7865.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1012_7865.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____7867 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____7867
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____7870 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____7870 with
                                         | (c2,g_lc) ->
                                             ((let uu____7882 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____7882
                                               then
                                                 let uu____7886 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____7886
                                               else ());
                                              (let uu____7891 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____7891))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_7900  ->
                              match uu___6_7900 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____7903 -> []))
                       in
                    let lc1 =
                      let uu____7905 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____7905 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1028_7907 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1028_7907.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1028_7907.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1028_7907.FStar_TypeChecker_Common.implicits)
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
        let uu____7943 =
          let uu____7946 =
            let uu____7951 =
              let uu____7952 =
                let uu____7961 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____7961  in
              [uu____7952]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____7951  in
          uu____7946 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____7943  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____7984 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____7984
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____8003 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____8019 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____8036 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____8036
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____8052)::(ens,uu____8054)::uu____8055 ->
                    let uu____8098 =
                      let uu____8101 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____8101  in
                    let uu____8102 =
                      let uu____8103 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____8103  in
                    (uu____8098, uu____8102)
                | uu____8106 ->
                    let uu____8117 =
                      let uu____8123 =
                        let uu____8125 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____8125
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____8123)
                       in
                    FStar_Errors.raise_error uu____8117
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____8145)::uu____8146 ->
                    let uu____8173 =
                      let uu____8178 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____8178
                       in
                    (match uu____8173 with
                     | (us_r,uu____8210) ->
                         let uu____8211 =
                           let uu____8216 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____8216
                            in
                         (match uu____8211 with
                          | (us_e,uu____8248) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____8251 =
                                  let uu____8252 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8252
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8251
                                  us_r
                                 in
                              let as_ens =
                                let uu____8254 =
                                  let uu____8255 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8255
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8254
                                  us_e
                                 in
                              let req =
                                let uu____8259 =
                                  let uu____8264 =
                                    let uu____8265 =
                                      let uu____8276 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8276]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8265
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____8264
                                   in
                                uu____8259 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____8316 =
                                  let uu____8321 =
                                    let uu____8322 =
                                      let uu____8333 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8333]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8322
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____8321
                                   in
                                uu____8316 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____8370 =
                                let uu____8373 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____8373  in
                              let uu____8374 =
                                let uu____8375 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____8375  in
                              (uu____8370, uu____8374)))
                | uu____8378 -> failwith "Impossible"))
  
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
      (let uu____8412 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____8412
       then
         let uu____8417 = FStar_Syntax_Print.term_to_string tm  in
         let uu____8419 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____8417 uu____8419
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
        (let uu____8473 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____8473
         then
           let uu____8478 = FStar_Syntax_Print.term_to_string tm  in
           let uu____8480 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____8478
             uu____8480
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____8491 =
      let uu____8493 =
        let uu____8494 = FStar_Syntax_Subst.compress t  in
        uu____8494.FStar_Syntax_Syntax.n  in
      match uu____8493 with
      | FStar_Syntax_Syntax.Tm_app uu____8498 -> false
      | uu____8516 -> true  in
    if uu____8491
    then t
    else
      (let uu____8521 = FStar_Syntax_Util.head_and_args t  in
       match uu____8521 with
       | (head1,args) ->
           let uu____8564 =
             let uu____8566 =
               let uu____8567 = FStar_Syntax_Subst.compress head1  in
               uu____8567.FStar_Syntax_Syntax.n  in
             match uu____8566 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____8572 -> false  in
           if uu____8564
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____8604 ->
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
          ((let uu____8651 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____8651
            then
              let uu____8654 = FStar_Syntax_Print.term_to_string e  in
              let uu____8656 = FStar_Syntax_Print.term_to_string t  in
              let uu____8658 =
                let uu____8660 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____8660
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____8654 uu____8656 uu____8658
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____8673 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____8673 with
              | (formals,uu____8689) ->
                  let n_implicits =
                    let uu____8711 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____8789  ->
                              match uu____8789 with
                              | (uu____8797,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____8804 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____8804 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____8711 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____8929 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____8929 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____8943 =
                      let uu____8949 =
                        let uu____8951 = FStar_Util.string_of_int n_expected
                           in
                        let uu____8953 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____8955 = FStar_Util.string_of_int n_available
                           in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____8951 uu____8953 uu____8955
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____8949)
                       in
                    let uu____8959 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____8943 uu____8959
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_8977 =
              match uu___7_8977 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____9020 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____9020 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _9151,uu____9138) when
                           _9151 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____9184,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Implicit
                                      uu____9186))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____9220 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____9220 with
                            | (v1,uu____9261,g) ->
                                ((let uu____9276 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____9276
                                  then
                                    let uu____9279 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____9279
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____9289 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____9289 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____9382 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____9382))))
                       | (uu____9409,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____9446 =
                             let uu____9459 =
                               let uu____9466 =
                                 let uu____9471 = FStar_Dyn.mkdyn env  in
                                 (uu____9471, tau)  in
                               FStar_Pervasives_Native.Some uu____9466  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____9459
                              in
                           (match uu____9446 with
                            | (v1,uu____9504,g) ->
                                ((let uu____9519 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____9519
                                  then
                                    let uu____9522 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____9522
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____9532 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____9532 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____9625 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____9625))))
                       | (uu____9652,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____9700 =
                       let uu____9727 = inst_n_binders t1  in
                       aux [] uu____9727 bs1  in
                     (match uu____9700 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____9799) -> (e, torig, guard)
                           | (uu____9830,[]) when
                               let uu____9861 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____9861 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____9863 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____9891 ->
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
            | uu____9904 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____9916 =
      let uu____9920 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____9920
        (FStar_List.map
           (fun u  ->
              let uu____9932 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____9932 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____9916 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____9960 = FStar_Util.set_is_empty x  in
      if uu____9960
      then []
      else
        (let s =
           let uu____9978 =
             let uu____9981 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____9981  in
           FStar_All.pipe_right uu____9978 FStar_Util.set_elements  in
         (let uu____9997 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____9997
          then
            let uu____10002 =
              let uu____10004 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____10004  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____10002
          else ());
         (let r =
            let uu____10013 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____10013  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____10052 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____10052
                     then
                       let uu____10057 =
                         let uu____10059 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____10059
                          in
                       let uu____10063 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____10065 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____10057 uu____10063 uu____10065
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
        let uu____10095 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____10095 FStar_Util.set_elements  in
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
        | ([],uu____10134) -> generalized_univ_names
        | (uu____10141,[]) -> explicit_univ_names
        | uu____10148 ->
            let uu____10157 =
              let uu____10163 =
                let uu____10165 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____10165
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____10163)
               in
            FStar_Errors.raise_error uu____10157 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____10187 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____10187
       then
         let uu____10192 = FStar_Syntax_Print.term_to_string t  in
         let uu____10194 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____10192 uu____10194
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____10203 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____10203
        then
          let uu____10208 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____10208
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____10217 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____10217
         then
           let uu____10222 = FStar_Syntax_Print.term_to_string t  in
           let uu____10224 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____10222 uu____10224
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
        let uu____10308 =
          let uu____10310 =
            FStar_Util.for_all
              (fun uu____10324  ->
                 match uu____10324 with
                 | (uu____10334,uu____10335,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____10310  in
        if uu____10308
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____10387 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____10387
              then
                let uu____10390 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____10390
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____10397 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____10397
               then
                 let uu____10400 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____10400
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____10418 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____10418 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____10452 =
             match uu____10452 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____10489 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____10489
                   then
                     let uu____10494 =
                       let uu____10496 =
                         let uu____10500 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____10500
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____10496
                         (FStar_String.concat ", ")
                        in
                     let uu____10548 =
                       let uu____10550 =
                         let uu____10554 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____10554
                           (FStar_List.map
                              (fun u  ->
                                 let uu____10567 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____10569 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____10567
                                   uu____10569))
                          in
                       FStar_All.pipe_right uu____10550
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____10494
                       uu____10548
                   else ());
                  (let univs2 =
                     let uu____10583 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____10595 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____10595) univs1
                       uu____10583
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____10602 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____10602
                    then
                      let uu____10607 =
                        let uu____10609 =
                          let uu____10613 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____10613
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____10609
                          (FStar_String.concat ", ")
                         in
                      let uu____10661 =
                        let uu____10663 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____10677 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____10679 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____10677
                                    uu____10679))
                           in
                        FStar_All.pipe_right uu____10663
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____10607 uu____10661
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____10700 =
             let uu____10717 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____10717  in
           match uu____10700 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____10807 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____10807
                 then ()
                 else
                   (let uu____10812 = lec_hd  in
                    match uu____10812 with
                    | (lb1,uu____10820,uu____10821) ->
                        let uu____10822 = lec2  in
                        (match uu____10822 with
                         | (lb2,uu____10830,uu____10831) ->
                             let msg =
                               let uu____10834 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10836 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____10834 uu____10836
                                in
                             let uu____10839 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____10839))
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
                 let uu____10907 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____10907
                 then ()
                 else
                   (let uu____10912 = lec_hd  in
                    match uu____10912 with
                    | (lb1,uu____10920,uu____10921) ->
                        let uu____10922 = lec2  in
                        (match uu____10922 with
                         | (lb2,uu____10930,uu____10931) ->
                             let msg =
                               let uu____10934 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10936 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____10934 uu____10936
                                in
                             let uu____10939 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____10939))
                  in
               let lecs1 =
                 let uu____10950 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____11003 = univs_and_uvars_of_lec this_lec  in
                        match uu____11003 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____10950 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____11108 = lec_hd  in
                   match uu____11108 with
                   | (lbname,e,c) ->
                       let uu____11118 =
                         let uu____11124 =
                           let uu____11126 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____11128 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____11130 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____11126 uu____11128 uu____11130
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____11124)
                          in
                       let uu____11134 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____11118 uu____11134
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____11153 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____11153 with
                         | FStar_Pervasives_Native.Some uu____11162 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____11170 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____11174 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____11174 with
                              | (bs,kres) ->
                                  ((let uu____11218 =
                                      let uu____11219 =
                                        let uu____11222 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____11222
                                         in
                                      uu____11219.FStar_Syntax_Syntax.n  in
                                    match uu____11218 with
                                    | FStar_Syntax_Syntax.Tm_type uu____11223
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____11227 =
                                          let uu____11229 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____11229  in
                                        if uu____11227
                                        then fail1 kres
                                        else ()
                                    | uu____11234 -> fail1 kres);
                                   (let a =
                                      let uu____11236 =
                                        let uu____11239 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _11242  ->
                                             FStar_Pervasives_Native.Some
                                               _11242) uu____11239
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____11236
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____11250 ->
                                          let uu____11259 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____11259
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
                      (fun uu____11362  ->
                         match uu____11362 with
                         | (lbname,e,c) ->
                             let uu____11408 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____11469 ->
                                   let uu____11482 = (e, c)  in
                                   (match uu____11482 with
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
                                                (fun uu____11522  ->
                                                   match uu____11522 with
                                                   | (x,uu____11528) ->
                                                       let uu____11529 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____11529)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____11547 =
                                                let uu____11549 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____11549
                                                 in
                                              if uu____11547
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
                                          let uu____11558 =
                                            let uu____11559 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____11559.FStar_Syntax_Syntax.n
                                             in
                                          match uu____11558 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____11584 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____11584 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____11595 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____11599 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____11599, gen_tvars))
                                in
                             (match uu____11408 with
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
        (let uu____11746 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____11746
         then
           let uu____11749 =
             let uu____11751 =
               FStar_List.map
                 (fun uu____11766  ->
                    match uu____11766 with
                    | (lb,uu____11775,uu____11776) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____11751 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____11749
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____11802  ->
                match uu____11802 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____11831 = gen env is_rec lecs  in
           match uu____11831 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____11930  ->
                       match uu____11930 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____11992 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____11992
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____12040  ->
                           match uu____12040 with
                           | (l,us,e,c,gvs) ->
                               let uu____12074 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____12076 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____12078 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____12080 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____12082 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____12074 uu____12076 uu____12078
                                 uu____12080 uu____12082))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____12127  ->
                match uu____12127 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____12171 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____12171, t, c, gvs)) univnames_lecs
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
              (let uu____12232 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____12232 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____12238 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _12241  -> FStar_Pervasives_Native.Some _12241)
                     uu____12238)
             in
          let is_var e1 =
            let uu____12249 =
              let uu____12250 = FStar_Syntax_Subst.compress e1  in
              uu____12250.FStar_Syntax_Syntax.n  in
            match uu____12249 with
            | FStar_Syntax_Syntax.Tm_name uu____12254 -> true
            | uu____12256 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1484_12277 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1484_12277.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1484_12277.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____12278 -> e2  in
          let env2 =
            let uu___1487_12280 = env1  in
            let uu____12281 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1487_12280.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1487_12280.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1487_12280.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1487_12280.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1487_12280.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1487_12280.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1487_12280.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1487_12280.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1487_12280.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1487_12280.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1487_12280.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1487_12280.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1487_12280.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1487_12280.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1487_12280.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1487_12280.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1487_12280.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____12281;
              FStar_TypeChecker_Env.is_iface =
                (uu___1487_12280.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1487_12280.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1487_12280.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1487_12280.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1487_12280.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1487_12280.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1487_12280.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1487_12280.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1487_12280.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1487_12280.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1487_12280.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1487_12280.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1487_12280.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1487_12280.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1487_12280.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1487_12280.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1487_12280.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1487_12280.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1487_12280.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1487_12280.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1487_12280.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1487_12280.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1487_12280.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1487_12280.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1487_12280.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1487_12280.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1487_12280.FStar_TypeChecker_Env.strict_args_tab)
            }  in
          let uu____12283 = check1 env2 t1 t2  in
          match uu____12283 with
          | FStar_Pervasives_Native.None  ->
              let uu____12290 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____12296 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____12290 uu____12296
          | FStar_Pervasives_Native.Some g ->
              ((let uu____12303 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12303
                then
                  let uu____12308 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____12308
                else ());
               (let uu____12314 = decorate e t2  in (uu____12314, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____12342 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____12342
         then
           let uu____12345 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____12345
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____12359 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____12359 with
         | (c,g_c) ->
             let uu____12371 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____12371
             then
               let uu____12379 =
                 let uu____12381 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____12381  in
               (uu____12379, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____12389 =
                    let uu____12390 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____12390
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____12389
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____12391 = check_trivial_precondition env c1  in
                match uu____12391 with
                | (ct,vc,g_pre) ->
                    ((let uu____12407 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____12407
                      then
                        let uu____12412 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____12412
                      else ());
                     (let uu____12417 =
                        let uu____12419 =
                          let uu____12420 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____12420  in
                        discharge uu____12419  in
                      let uu____12421 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____12417, uu____12421)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_12455 =
        match uu___8_12455 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____12465)::[] -> f fst1
        | uu____12490 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____12502 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____12502
          (fun _12503  -> FStar_TypeChecker_Common.NonTrivial _12503)
         in
      let op_or_e e =
        let uu____12514 =
          let uu____12515 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____12515  in
        FStar_All.pipe_right uu____12514
          (fun _12518  -> FStar_TypeChecker_Common.NonTrivial _12518)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _12525  -> FStar_TypeChecker_Common.NonTrivial _12525)
         in
      let op_or_t t =
        let uu____12536 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____12536
          (fun _12539  -> FStar_TypeChecker_Common.NonTrivial _12539)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _12546  -> FStar_TypeChecker_Common.NonTrivial _12546)
         in
      let short_op_ite uu___9_12552 =
        match uu___9_12552 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____12562)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____12589)::[] ->
            let uu____12630 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____12630
              (fun _12631  -> FStar_TypeChecker_Common.NonTrivial _12631)
        | uu____12632 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____12644 =
          let uu____12652 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____12652)  in
        let uu____12660 =
          let uu____12670 =
            let uu____12678 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____12678)  in
          let uu____12686 =
            let uu____12696 =
              let uu____12704 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____12704)  in
            let uu____12712 =
              let uu____12722 =
                let uu____12730 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____12730)  in
              let uu____12738 =
                let uu____12748 =
                  let uu____12756 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____12756)  in
                [uu____12748; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____12722 :: uu____12738  in
            uu____12696 :: uu____12712  in
          uu____12670 :: uu____12686  in
        uu____12644 :: uu____12660  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____12818 =
            FStar_Util.find_map table
              (fun uu____12833  ->
                 match uu____12833 with
                 | (x,mk1) ->
                     let uu____12850 = FStar_Ident.lid_equals x lid  in
                     if uu____12850
                     then
                       let uu____12855 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____12855
                     else FStar_Pervasives_Native.None)
             in
          (match uu____12818 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____12859 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____12867 =
      let uu____12868 = FStar_Syntax_Util.un_uinst l  in
      uu____12868.FStar_Syntax_Syntax.n  in
    match uu____12867 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____12873 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____12909)::uu____12910 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____12929 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____12938,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____12939))::uu____12940 -> bs
      | uu____12958 ->
          let uu____12959 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____12959 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____12963 =
                 let uu____12964 = FStar_Syntax_Subst.compress t  in
                 uu____12964.FStar_Syntax_Syntax.n  in
               (match uu____12963 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____12968) ->
                    let uu____12989 =
                      FStar_Util.prefix_until
                        (fun uu___10_13029  ->
                           match uu___10_13029 with
                           | (uu____13037,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____13038)) ->
                               false
                           | uu____13043 -> true) bs'
                       in
                    (match uu____12989 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____13079,uu____13080) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____13152,uu____13153) ->
                         let uu____13226 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____13246  ->
                                   match uu____13246 with
                                   | (x,uu____13255) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____13226
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____13304  ->
                                     match uu____13304 with
                                     | (x,i) ->
                                         let uu____13323 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____13323, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____13334 -> bs))
  
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
            let uu____13363 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____13363
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
          let uu____13394 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____13394
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
        (let uu____13437 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____13437
         then
           ((let uu____13442 = FStar_Ident.text_of_lid lident  in
             d uu____13442);
            (let uu____13444 = FStar_Ident.text_of_lid lident  in
             let uu____13446 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____13444 uu____13446))
         else ());
        (let fv =
           let uu____13452 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____13452
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
         let uu____13464 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1644_13466 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1644_13466.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1644_13466.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1644_13466.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1644_13466.FStar_Syntax_Syntax.sigattrs)
           }), uu____13464))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_13484 =
        match uu___11_13484 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____13487 -> false  in
      let reducibility uu___12_13495 =
        match uu___12_13495 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____13502 -> false  in
      let assumption uu___13_13510 =
        match uu___13_13510 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____13514 -> false  in
      let reification uu___14_13522 =
        match uu___14_13522 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____13525 -> true
        | uu____13527 -> false  in
      let inferred uu___15_13535 =
        match uu___15_13535 with
        | FStar_Syntax_Syntax.Discriminator uu____13537 -> true
        | FStar_Syntax_Syntax.Projector uu____13539 -> true
        | FStar_Syntax_Syntax.RecordType uu____13545 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____13555 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____13568 -> false  in
      let has_eq uu___16_13576 =
        match uu___16_13576 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____13580 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____13659 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____13666 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____13677 =
        let uu____13679 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___17_13685  ->
                  match uu___17_13685 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____13688 -> false))
           in
        FStar_All.pipe_right uu____13679 Prims.op_Negation  in
      if uu____13677
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____13709 =
            let uu____13715 =
              let uu____13717 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____13717 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____13715)  in
          FStar_Errors.raise_error uu____13709 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____13735 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____13743 =
            let uu____13745 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____13745  in
          if uu____13743 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____13755),uu____13756) ->
              ((let uu____13768 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____13768
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____13777 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____13777
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____13788 ->
              let uu____13797 =
                let uu____13799 =
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
                Prims.op_Negation uu____13799  in
              if uu____13797 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____13809 ->
              let uu____13816 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____13816 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____13824 ->
              let uu____13831 =
                let uu____13833 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____13833  in
              if uu____13831 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____13843 ->
              let uu____13844 =
                let uu____13846 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____13846  in
              if uu____13844 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13856 ->
              let uu____13857 =
                let uu____13859 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____13859  in
              if uu____13857 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13869 ->
              let uu____13882 =
                let uu____13884 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____13884  in
              if uu____13882 then err'1 () else ()
          | uu____13894 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let has_erased_for_extraction_attr fv =
        let uu____13917 =
          let uu____13922 =
            FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
          FStar_All.pipe_right uu____13922
            (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
           in
        FStar_All.pipe_right uu____13917
          (fun l_opt  ->
             (FStar_Util.is_some l_opt) &&
               (let uu____13941 = FStar_All.pipe_right l_opt FStar_Util.must
                   in
                FStar_All.pipe_right uu____13941
                  (FStar_List.existsb
                     (fun t1  ->
                        let uu____13959 =
                          let uu____13960 = FStar_Syntax_Subst.compress t1
                             in
                          uu____13960.FStar_Syntax_Syntax.n  in
                        match uu____13959 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            FStar_Ident.lid_equals
                              (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              FStar_Parser_Const.must_erase_for_extraction_attr
                            -> true
                        | uu____13966 -> false))))
         in
      let rec aux_whnf env t1 =
        let uu____13992 =
          let uu____13993 = FStar_Syntax_Subst.compress t1  in
          uu____13993.FStar_Syntax_Syntax.n  in
        match uu____13992 with
        | FStar_Syntax_Syntax.Tm_type uu____13997 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (has_erased_for_extraction_attr fv)
        | FStar_Syntax_Syntax.Tm_arrow uu____14000 ->
            let uu____14015 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____14015 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____14048 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____14048
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____14054;
               FStar_Syntax_Syntax.index = uu____14055;
               FStar_Syntax_Syntax.sort = t2;_},uu____14057)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14066,uu____14067) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____14109::[]) ->
            let uu____14148 =
              let uu____14149 = FStar_Syntax_Util.un_uinst head1  in
              uu____14149.FStar_Syntax_Syntax.n  in
            (match uu____14148 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.erased_lid)
                   || (has_erased_for_extraction_attr fv)
             | uu____14154 -> false)
        | uu____14156 -> false
      
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
        (let uu____14166 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____14166
         then
           let uu____14171 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____14171
         else ());
        res
       in aux g t
  
let (fresh_non_layered_effect_repr :
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
            let wp_sort =
              let signature =
                FStar_TypeChecker_Env.lookup_effect_lid env eff_name  in
              let uu____14218 =
                let uu____14219 = FStar_Syntax_Subst.compress signature  in
                uu____14219.FStar_Syntax_Syntax.n  in
              match uu____14218 with
              | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14223) when
                  (FStar_List.length bs) = (Prims.of_int (2)) ->
                  let uu____14252 = FStar_Syntax_Subst.open_binders bs  in
                  (match uu____14252 with
                   | (a,uu____14254)::(wp,uu____14256)::[] ->
                       FStar_All.pipe_right wp.FStar_Syntax_Syntax.sort
                         (FStar_Syntax_Subst.subst
                            [FStar_Syntax_Syntax.NT (a, a_tm)]))
              | uu____14285 ->
                  let uu____14286 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name signature
                     in
                  FStar_Errors.raise_error uu____14286 r
               in
            let uu____14292 =
              let uu____14305 =
                let uu____14307 = FStar_Range.string_of_range r  in
                FStar_Util.format2 "implicit for wp of %s at %s"
                  eff_name.FStar_Ident.str uu____14307
                 in
              new_implicit_var uu____14305 r env wp_sort  in
            match uu____14292 with
            | (wp_uvar,uu____14315,g_wp_uvar) ->
                let eff_c =
                  let uu____14330 =
                    let uu____14331 =
                      let uu____14342 =
                        FStar_All.pipe_right wp_uvar
                          FStar_Syntax_Syntax.as_arg
                         in
                      [uu____14342]  in
                    {
                      FStar_Syntax_Syntax.comp_univs = [u];
                      FStar_Syntax_Syntax.effect_name = eff_name;
                      FStar_Syntax_Syntax.result_typ = a_tm;
                      FStar_Syntax_Syntax.effect_args = uu____14331;
                      FStar_Syntax_Syntax.flags = []
                    }  in
                  FStar_Syntax_Syntax.mk_Comp uu____14330  in
                let uu____14375 =
                  let uu____14376 =
                    let uu____14383 =
                      let uu____14384 =
                        let uu____14399 =
                          let uu____14408 =
                            FStar_Syntax_Syntax.null_binder
                              FStar_Syntax_Syntax.t_unit
                             in
                          [uu____14408]  in
                        (uu____14399, eff_c)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____14384  in
                    FStar_Syntax_Syntax.mk uu____14383  in
                  uu____14376 FStar_Pervasives_Native.None r  in
                (uu____14375, g_wp_uvar)
  
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
                  let uu____14487 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____14487 r  in
                let uu____14497 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____14497 with
                | (uu____14506,signature) ->
                    let uu____14508 =
                      let uu____14509 = FStar_Syntax_Subst.compress signature
                         in
                      uu____14509.FStar_Syntax_Syntax.n  in
                    (match uu____14508 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14517) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____14565 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____14580 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____14582 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____14580 eff_name.FStar_Ident.str
                                       uu____14582) r
                                 in
                              (match uu____14565 with
                               | (is,g) ->
                                   let repr =
                                     let uu____14596 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts [u]
                                        in
                                     FStar_All.pipe_right uu____14596
                                       FStar_Pervasives_Native.snd
                                      in
                                   let uu____14605 =
                                     let uu____14606 =
                                       let uu____14611 =
                                         FStar_List.map
                                           FStar_Syntax_Syntax.as_arg (a_tm
                                           :: is)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr
                                         uu____14611
                                        in
                                     uu____14606 FStar_Pervasives_Native.None
                                       r
                                      in
                                   (uu____14605, g))
                          | uu____14620 -> fail1 signature)
                     | uu____14621 -> fail1 signature)
  
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
            let uu____14652 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____14652
              (fun ed  ->
                 if ed.FStar_Syntax_Syntax.is_layered
                 then
                   fresh_layered_effect_repr env r eff_name
                     ed.FStar_Syntax_Syntax.signature
                     ed.FStar_Syntax_Syntax.repr u a_tm
                 else fresh_non_layered_effect_repr env r eff_name u a_tm)
  
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
              let uu____14697 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____14697 with
              | (uu____14702,sig_tm) ->
                  let fail1 t =
                    let uu____14710 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____14710 r  in
                  let uu____14716 =
                    let uu____14717 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____14717.FStar_Syntax_Syntax.n  in
                  (match uu____14716 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14721) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____14744)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____14766 -> fail1 sig_tm)
                   | uu____14767 -> fail1 sig_tm)
  
let (lift_tf_layered_effect :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.tscheme -> FStar_TypeChecker_Env.lift_comp_t)
  =
  fun tgt  ->
    fun lift_ts  ->
      fun env  ->
        fun c  ->
          (let uu____14788 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____14788
           then
             let uu____14793 = FStar_Syntax_Print.comp_to_string c  in
             let uu____14795 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____14793 uu____14795
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let effect_args_from_repr repr is_layered =
             let err uu____14825 =
               let uu____14826 =
                 let uu____14832 =
                   let uu____14834 = FStar_Syntax_Print.term_to_string repr
                      in
                   let uu____14836 = FStar_Util.string_of_bool is_layered  in
                   FStar_Util.format2
                     "Could not get effect args from repr %s with is_layered %s"
                     uu____14834 uu____14836
                    in
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____14832)  in
               FStar_Errors.raise_error uu____14826 r  in
             let repr1 = FStar_Syntax_Subst.compress repr  in
             if is_layered
             then
               match repr1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_app (uu____14848,uu____14849::is) ->
                   FStar_All.pipe_right is
                     (FStar_List.map FStar_Pervasives_Native.fst)
               | uu____14917 -> err ()
             else
               (match repr1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (uu____14922,c1) ->
                    let uu____14944 =
                      FStar_All.pipe_right c1
                        FStar_Syntax_Util.comp_to_comp_typ
                       in
                    FStar_All.pipe_right uu____14944
                      (fun ct  ->
                         FStar_All.pipe_right
                           ct.FStar_Syntax_Syntax.effect_args
                           (FStar_List.map FStar_Pervasives_Native.fst))
                | uu____14979 -> err ())
              in
           let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____14981 =
             let uu____14992 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____14993 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____14992, (ct.FStar_Syntax_Syntax.result_typ), uu____14993)
              in
           match uu____14981 with
           | (u,a,c_is) ->
               let uu____15041 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____15041 with
                | (uu____15050,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____15061 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____15063 = FStar_Ident.string_of_lid tgt  in
                      let uu____15065 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____15061 uu____15063 s uu____15065
                       in
                    let uu____15068 =
                      let uu____15101 =
                        let uu____15102 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____15102.FStar_Syntax_Syntax.n  in
                      match uu____15101 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____15166 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____15166 with
                           | (a_b::bs1,c2) ->
                               let uu____15226 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               let uu____15288 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____15226, uu____15288))
                      | uu____15315 ->
                          let uu____15316 =
                            let uu____15322 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____15322)
                             in
                          FStar_Errors.raise_error uu____15316 r
                       in
                    (match uu____15068 with
                     | (a_b,(rest_bs,f_b::[]),lift_ct) ->
                         let uu____15440 =
                           let uu____15447 =
                             let uu____15448 =
                               let uu____15449 =
                                 let uu____15456 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____15456, a)  in
                               FStar_Syntax_Syntax.NT uu____15449  in
                             [uu____15448]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____15447
                             (fun b  ->
                                let uu____15473 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____15475 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____15477 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____15479 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____15473 uu____15475 uu____15477
                                  uu____15479) r
                            in
                         (match uu____15440 with
                          | (rest_bs_uvars,g) ->
                              let substs =
                                FStar_List.map2
                                  (fun b  ->
                                     fun t  ->
                                       let uu____15516 =
                                         let uu____15523 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____15523, t)  in
                                       FStar_Syntax_Syntax.NT uu____15516)
                                  (a_b :: rest_bs) (a :: rest_bs_uvars)
                                 in
                              let guard_f =
                                let f_sort =
                                  let uu____15542 =
                                    FStar_All.pipe_right
                                      (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                      (FStar_Syntax_Subst.subst substs)
                                     in
                                  FStar_All.pipe_right uu____15542
                                    FStar_Syntax_Subst.compress
                                   in
                                let f_sort_is =
                                  let uu____15548 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env ct.FStar_Syntax_Syntax.effect_name
                                     in
                                  effect_args_from_repr f_sort uu____15548
                                   in
                                FStar_List.fold_left2
                                  (fun g1  ->
                                     fun i1  ->
                                       fun i2  ->
                                         let uu____15557 =
                                           FStar_TypeChecker_Rel.teq env i1
                                             i2
                                            in
                                         FStar_TypeChecker_Env.conj_guard g1
                                           uu____15557)
                                  FStar_TypeChecker_Env.trivial_guard c_is
                                  f_sort_is
                                 in
                              let is =
                                let uu____15561 =
                                  FStar_TypeChecker_Env.is_layered_effect env
                                    tgt
                                   in
                                effect_args_from_repr
                                  lift_ct.FStar_Syntax_Syntax.result_typ
                                  uu____15561
                                 in
                              let c1 =
                                let uu____15564 =
                                  let uu____15565 =
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      is
                                     in
                                  {
                                    FStar_Syntax_Syntax.comp_univs =
                                      (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                    FStar_Syntax_Syntax.effect_name = tgt;
                                    FStar_Syntax_Syntax.result_typ = a;
                                    FStar_Syntax_Syntax.effect_args =
                                      uu____15565;
                                    FStar_Syntax_Syntax.flags =
                                      (ct.FStar_Syntax_Syntax.flags)
                                  }  in
                                FStar_Syntax_Syntax.mk_Comp uu____15564  in
                              ((let uu____15585 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____15585
                                then
                                  let uu____15590 =
                                    FStar_Syntax_Print.comp_to_string c1  in
                                  FStar_Util.print1 "} Lifted comp: %s\n"
                                    uu____15590
                                else ());
                               (let uu____15595 =
                                  FStar_TypeChecker_Env.conj_guard g guard_f
                                   in
                                (c1, uu____15595)))))))
  