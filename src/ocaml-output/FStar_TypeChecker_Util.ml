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
                                         let x_a =
                                           match b1 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Syntax_Syntax.null_binder
                                                 ct1.FStar_Syntax_Syntax.result_typ
                                           | FStar_Pervasives_Native.Some x
                                               ->
                                               FStar_Syntax_Syntax.mk_binder
                                                 x
                                            in
                                         let uu____3738 =
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
                                           let uu____3749 =
                                             FStar_TypeChecker_Env.monad_leq
                                               env
                                               c1_ed.FStar_Syntax_Syntax.mname
                                               c2_ed.FStar_Syntax_Syntax.mname
                                              in
                                           match uu____3749 with
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____3760 =
                                                 FStar_TypeChecker_Env.monad_leq
                                                   env
                                                   c2_ed.FStar_Syntax_Syntax.mname
                                                   c1_ed.FStar_Syntax_Syntax.mname
                                                  in
                                               (match uu____3760 with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    let uu____3771 =
                                                      let uu____3777 =
                                                        FStar_Util.format2
                                                          "Effects %s and %s cannot be composed"
                                                          (c1_ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                          (c2_ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                         in
                                                      (FStar_Errors.Fatal_EffectsCannotBeComposed,
                                                        uu____3777)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____3771 r1
                                                | FStar_Pervasives_Native.Some
                                                    edge ->
                                                    let env_l =
                                                      FStar_TypeChecker_Env.push_binders
                                                        env [x_a]
                                                       in
                                                    let uu____3803 =
                                                      let uu____3808 =
                                                        let uu____3813 =
                                                          FStar_All.pipe_right
                                                            ct2
                                                            FStar_Syntax_Syntax.mk_Comp
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____3813
                                                          ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                             env_l)
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3808
                                                        (fun uu____3830  ->
                                                           match uu____3830
                                                           with
                                                           | (c,g) ->
                                                               let uu____3841
                                                                 =
                                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                                   c
                                                                  in
                                                               (uu____3841,
                                                                 g))
                                                       in
                                                    (match uu____3803 with
                                                     | (ct21,g_lift) ->
                                                         let uu____3852 =
                                                           FStar_TypeChecker_Env.close_guard
                                                             env [x_a] g_lift
                                                            in
                                                         (ct1, ct21, c1_ed,
                                                           uu____3852)))
                                           | FStar_Pervasives_Native.Some
                                               edge ->
                                               let uu____3866 =
                                                 let uu____3871 =
                                                   let uu____3876 =
                                                     FStar_All.pipe_right ct1
                                                       FStar_Syntax_Syntax.mk_Comp
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3876
                                                     ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                        env)
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3871
                                                   (fun uu____3893  ->
                                                      match uu____3893 with
                                                      | (c,g) ->
                                                          let uu____3904 =
                                                            FStar_Syntax_Util.comp_to_comp_typ
                                                              c
                                                             in
                                                          (uu____3904, g))
                                                  in
                                               (match uu____3866 with
                                                | (ct11,g_lift) ->
                                                    (ct11, ct2, c2_ed,
                                                      g_lift))
                                            in
                                         match uu____3738 with
                                         | (ct11,ct21,ed,g_lift) ->
                                             ((let uu____3924 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____3924
                                               then
                                                 let uu____3929 =
                                                   let uu____3931 =
                                                     FStar_All.pipe_right
                                                       ct11
                                                       FStar_Syntax_Syntax.mk_Comp
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3931
                                                     FStar_Syntax_Print.comp_to_string
                                                    in
                                                 let uu____3933 =
                                                   let uu____3935 =
                                                     FStar_All.pipe_right
                                                       ct21
                                                       FStar_Syntax_Syntax.mk_Comp
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3935
                                                     FStar_Syntax_Print.comp_to_string
                                                    in
                                                 FStar_Util.print2
                                                   "After lifting, ct1: %s and ct2: %s\n"
                                                   uu____3929 uu____3933
                                               else ());
                                              (let uu____3940 =
                                                 let uu____3951 =
                                                   FStar_List.hd
                                                     ct11.FStar_Syntax_Syntax.comp_univs
                                                    in
                                                 let uu____3952 =
                                                   FStar_List.map
                                                     FStar_Pervasives_Native.fst
                                                     ct11.FStar_Syntax_Syntax.effect_args
                                                    in
                                                 (uu____3951,
                                                   (ct11.FStar_Syntax_Syntax.result_typ),
                                                   uu____3952)
                                                  in
                                               match uu____3940 with
                                               | (u1,t1,is1) ->
                                                   let uu____3986 =
                                                     let uu____3997 =
                                                       FStar_List.hd
                                                         ct21.FStar_Syntax_Syntax.comp_univs
                                                        in
                                                     let uu____3998 =
                                                       FStar_List.map
                                                         FStar_Pervasives_Native.fst
                                                         ct21.FStar_Syntax_Syntax.effect_args
                                                        in
                                                     (uu____3997,
                                                       (ct21.FStar_Syntax_Syntax.result_typ),
                                                       uu____3998)
                                                      in
                                                   (match uu____3986 with
                                                    | (u2,t2,is2) ->
                                                        let uu____4032 =
                                                          FStar_TypeChecker_Env.inst_tscheme_with
                                                            ed.FStar_Syntax_Syntax.bind_wp
                                                            [u1; u2]
                                                           in
                                                        (match uu____4032
                                                         with
                                                         | (uu____4041,bind_t)
                                                             ->
                                                             let bind_t_shape_error
                                                               s =
                                                               let uu____4056
                                                                 =
                                                                 let uu____4058
                                                                   =
                                                                   FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                    in
                                                                 FStar_Util.format2
                                                                   "bind %s does not have proper shape (reason:%s)"
                                                                   uu____4058
                                                                   s
                                                                  in
                                                               (FStar_Errors.Fatal_UnexpectedEffect,
                                                                 uu____4056)
                                                                in
                                                             let uu____4062 =
                                                               let uu____4107
                                                                 =
                                                                 let uu____4108
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    bind_t
                                                                    in
                                                                 uu____4108.FStar_Syntax_Syntax.n
                                                                  in
                                                               match uu____4107
                                                               with
                                                               | FStar_Syntax_Syntax.Tm_arrow
                                                                   (bs,c)
                                                                   when
                                                                   (FStar_List.length
                                                                    bs) >=
                                                                    (Prims.of_int (4))
                                                                   ->
                                                                   let uu____4184
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                   (match uu____4184
                                                                    with
                                                                    | 
                                                                    (a_b::b_b::bs1,c3)
                                                                    ->
                                                                    let uu____4269
                                                                    =
                                                                    let uu____4296
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs1) -
                                                                    (Prims.of_int (2)))
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____4296
                                                                    (fun
                                                                    uu____4381
                                                                     ->
                                                                    match uu____4381
                                                                    with
                                                                    | 
                                                                    (l1,l2)
                                                                    ->
                                                                    let uu____4462
                                                                    =
                                                                    FStar_List.hd
                                                                    l2  in
                                                                    let uu____4475
                                                                    =
                                                                    let uu____4482
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                    FStar_List.hd
                                                                    uu____4482
                                                                     in
                                                                    (l1,
                                                                    uu____4462,
                                                                    uu____4475))
                                                                     in
                                                                    (match uu____4269
                                                                    with
                                                                    | 
                                                                    (rest_bs,f_b,g_b)
                                                                    ->
                                                                    let uu____4610
                                                                    =
                                                                    FStar_Syntax_Util.comp_to_comp_typ
                                                                    c3  in
                                                                    (a_b,
                                                                    b_b,
                                                                    rest_bs,
                                                                    f_b, g_b,
                                                                    uu____4610)))
                                                               | uu____4643
                                                                   ->
                                                                   let uu____4644
                                                                    =
                                                                    bind_t_shape_error
                                                                    "Either not an arrow or not enough binders"
                                                                     in
                                                                   FStar_Errors.raise_error
                                                                    uu____4644
                                                                    r1
                                                                in
                                                             (match uu____4062
                                                              with
                                                              | (a_b,b_b,rest_bs,f_b,g_b,bind_ct)
                                                                  ->
                                                                  let uu____4769
                                                                    =
                                                                    let uu____4776
                                                                    =
                                                                    let uu____4777
                                                                    =
                                                                    let uu____4778
                                                                    =
                                                                    let uu____4785
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    a_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    (uu____4785,
                                                                    t1)  in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4778
                                                                     in
                                                                    let uu____4796
                                                                    =
                                                                    let uu____4799
                                                                    =
                                                                    let uu____4800
                                                                    =
                                                                    let uu____4807
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    b_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    (uu____4807,
                                                                    t2)  in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4800
                                                                     in
                                                                    [uu____4799]
                                                                     in
                                                                    uu____4777
                                                                    ::
                                                                    uu____4796
                                                                     in
                                                                    FStar_TypeChecker_Env.uvars_for_binders
                                                                    env
                                                                    rest_bs
                                                                    uu____4776
                                                                    (fun b2 
                                                                    ->
                                                                    let uu____4822
                                                                    =
                                                                    FStar_Syntax_Print.binder_to_string
                                                                    b2  in
                                                                    let uu____4824
                                                                    =
                                                                    FStar_Range.string_of_range
                                                                    r1  in
                                                                    FStar_Util.format3
                                                                    "implicit var for binder %s of %s:bind at %s"
                                                                    uu____4822
                                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                                    uu____4824)
                                                                    r1  in
                                                                  (match uu____4769
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
                                                                    let uu____4861
                                                                    =
                                                                    let uu____4868
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    b2
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    (uu____4868,
                                                                    t)  in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4861)
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
                                                                    let uu____4895
                                                                    =
                                                                    let uu____4896
                                                                    =
                                                                    let uu____4899
                                                                    =
                                                                    let uu____4900
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    f_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    uu____4900.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_Syntax_Subst.compress
                                                                    uu____4899
                                                                     in
                                                                    uu____4896.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____4895
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____4911,uu____4912::is)
                                                                    ->
                                                                    let uu____4954
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4954
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1))
                                                                    | 
                                                                    uu____4987
                                                                    ->
                                                                    let uu____4988
                                                                    =
                                                                    bind_t_shape_error
                                                                    "f's type is not a repr type"
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____4988
                                                                    r1  in
                                                                    FStar_List.fold_left2
                                                                    (fun g 
                                                                    ->
                                                                    fun i1 
                                                                    ->
                                                                    fun f_i1 
                                                                    ->
                                                                    let uu____5004
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env i1
                                                                    f_i1  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____5004)
                                                                    FStar_TypeChecker_Env.trivial_guard
                                                                    is1
                                                                    f_sort_is
                                                                     in
                                                                    let g_guard
                                                                    =
                                                                    let g_sort_is
                                                                    =
                                                                    let uu____5009
                                                                    =
                                                                    let uu____5010
                                                                    =
                                                                    let uu____5013
                                                                    =
                                                                    let uu____5014
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    g_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    uu____5014.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_Syntax_Subst.compress
                                                                    uu____5013
                                                                     in
                                                                    uu____5010.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____5009
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____5047
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____5047
                                                                    with
                                                                    | 
                                                                    (bs1,c3)
                                                                    ->
                                                                    let bs_subst
                                                                    =
                                                                    let uu____5057
                                                                    =
                                                                    let uu____5064
                                                                    =
                                                                    let uu____5065
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____5065
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____5086
                                                                    =
                                                                    let uu____5089
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5089
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____5064,
                                                                    uu____5086)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____5057
                                                                     in
                                                                    let c4 =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c3  in
                                                                    let uu____5103
                                                                    =
                                                                    let uu____5104
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c4)  in
                                                                    uu____5104.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5103
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____5109,uu____5110::is)
                                                                    ->
                                                                    let uu____5152
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5152
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1))
                                                                    | 
                                                                    uu____5185
                                                                    ->
                                                                    let uu____5186
                                                                    =
                                                                    bind_t_shape_error
                                                                    "g's type is not a repr type"
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____5186
                                                                    r1))
                                                                    | 
                                                                    uu____5195
                                                                    ->
                                                                    let uu____5196
                                                                    =
                                                                    bind_t_shape_error
                                                                    "g's type is not an arrow"
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____5196
                                                                    r1  in
                                                                    let env_g
                                                                    =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env 
                                                                    [x_a]  in
                                                                    let uu____5218
                                                                    =
                                                                    FStar_List.fold_left2
                                                                    (fun g 
                                                                    ->
                                                                    fun i1 
                                                                    ->
                                                                    fun g_i1 
                                                                    ->
                                                                    let uu____5226
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env_g i1
                                                                    g_i1  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____5226)
                                                                    FStar_TypeChecker_Env.trivial_guard
                                                                    is2
                                                                    g_sort_is
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5218
                                                                    (FStar_TypeChecker_Env.close_guard
                                                                    env 
                                                                    [x_a])
                                                                     in
                                                                    let is =
                                                                    let uu____5242
                                                                    =
                                                                    let uu____5243
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    bind_ct.FStar_Syntax_Syntax.result_typ
                                                                     in
                                                                    uu____5243.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____5242
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____5248,uu____5249::is)
                                                                    ->
                                                                    let uu____5291
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5291
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1))
                                                                    | 
                                                                    uu____5324
                                                                    ->
                                                                    let uu____5325
                                                                    =
                                                                    bind_t_shape_error
                                                                    "return type is not a repr type"
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____5325
                                                                    r1  in
                                                                    let c =
                                                                    let uu____5335
                                                                    =
                                                                    let uu____5336
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
                                                                    uu____5336;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    uu____5335
                                                                     in
                                                                    ((
                                                                    let uu____5356
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "LayeredEffects")
                                                                     in
                                                                    if
                                                                    uu____5356
                                                                    then
                                                                    let uu____5361
                                                                    =
                                                                    FStar_Syntax_Print.comp_to_string
                                                                    c  in
                                                                    FStar_Util.print1
                                                                    "} c after bind: %s\n"
                                                                    uu____5361
                                                                    else ());
                                                                    (let uu____5366
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
                                                                    uu____5366))))))))))
                                         in
                                      let mk_bind c11 b1 c21 =
                                        let uu____5391 =
                                          lift_and_destruct env c11 c21  in
                                        match uu____5391 with
                                        | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2),g)
                                            ->
                                            let bs =
                                              match b1 with
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____5451 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      t1
                                                     in
                                                  [uu____5451]
                                              | FStar_Pervasives_Native.Some
                                                  x ->
                                                  let uu____5471 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____5471]
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
                                              let uu____5518 =
                                                FStar_Syntax_Syntax.as_arg
                                                  r11
                                                 in
                                              let uu____5527 =
                                                let uu____5538 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1
                                                   in
                                                let uu____5547 =
                                                  let uu____5558 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      t2
                                                     in
                                                  let uu____5567 =
                                                    let uu____5578 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        wp1
                                                       in
                                                    let uu____5587 =
                                                      let uu____5598 =
                                                        let uu____5607 =
                                                          mk_lam wp2  in
                                                        FStar_Syntax_Syntax.as_arg
                                                          uu____5607
                                                         in
                                                      [uu____5598]  in
                                                    uu____5578 :: uu____5587
                                                     in
                                                  uu____5558 :: uu____5567
                                                   in
                                                uu____5538 :: uu____5547  in
                                              uu____5518 :: uu____5527  in
                                            let wp =
                                              let uu____5659 =
                                                let uu____5664 =
                                                  FStar_TypeChecker_Env.inst_effect_fun_with
                                                    [u_t1; u_t2] env md
                                                    md.FStar_Syntax_Syntax.bind_wp
                                                   in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____5664 wp_args
                                                 in
                                              uu____5659
                                                FStar_Pervasives_Native.None
                                                t2.FStar_Syntax_Syntax.pos
                                               in
                                            let uu____5665 =
                                              mk_comp md u_t2 t2 wp
                                                bind_flags
                                               in
                                            let uu____5666 =
                                              let uu____5667 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g_c1 g_c2
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                uu____5667 g
                                               in
                                            (uu____5665, uu____5666)
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
                                        let uu____5694 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____5694 with
                                        | (m,uu____5706,lift2) ->
                                            let uu____5708 =
                                              let uu____5713 =
                                                lift_comp env c22 lift2  in
                                              FStar_All.pipe_right uu____5713
                                                (fun uu____5730  ->
                                                   match uu____5730 with
                                                   | (c,g) ->
                                                       let uu____5741 =
                                                         FStar_Syntax_Syntax.mk_Comp
                                                           c
                                                          in
                                                       (uu____5741, g))
                                               in
                                            (match uu____5708 with
                                             | (c23,g2) ->
                                                 let uu____5748 =
                                                   destruct_comp c12  in
                                                 (match uu____5748 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let vc1 =
                                                        let uu____5766 =
                                                          let uu____5771 =
                                                            let uu____5772 =
                                                              FStar_All.pipe_right
                                                                md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                                                FStar_Util.must
                                                               in
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              uu____5772
                                                             in
                                                          let uu____5775 =
                                                            let uu____5776 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____5785 =
                                                              let uu____5796
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____5796]
                                                               in
                                                            uu____5776 ::
                                                              uu____5785
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____5771
                                                            uu____5775
                                                           in
                                                        uu____5766
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____5829 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      let uu____5834 =
                                                        let uu____5835 =
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g_c1 g_c2
                                                           in
                                                        FStar_TypeChecker_Env.conj_guard
                                                          uu____5835 g2
                                                         in
                                                      (uu____5829,
                                                        uu____5834)))
                                         in
                                      let uu____5836 =
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
                                      if uu____5836
                                      then mk_layered_bind c1 b c2
                                      else
                                        (let c1_typ =
                                           FStar_TypeChecker_Env.unfold_effect_abbrev
                                             env c1
                                            in
                                         let uu____5848 =
                                           destruct_comp c1_typ  in
                                         match uu____5848 with
                                         | (u_res_t1,res_t1,uu____5861) ->
                                             let uu____5862 =
                                               (FStar_Option.isSome b) &&
                                                 (should_return env e1opt
                                                    lc11)
                                                in
                                             if uu____5862
                                             then
                                               let e1 =
                                                 FStar_Option.get e1opt  in
                                               let x = FStar_Option.get b  in
                                               let uu____5871 =
                                                 FStar_Syntax_Util.is_partial_return
                                                   c1
                                                  in
                                               (if uu____5871
                                                then
                                                  (debug1
                                                     (fun uu____5885  ->
                                                        let uu____5886 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____5888 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case a): Substituting %s for %s"
                                                          uu____5886
                                                          uu____5888);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    mk_bind c1 b c21))
                                                else
                                                  (let uu____5896 =
                                                     ((FStar_Options.vcgen_optimize_bind_as_seq
                                                         ())
                                                        &&
                                                        (lcomp_has_trivial_postcondition
                                                           lc11))
                                                       &&
                                                       (let uu____5899 =
                                                          FStar_TypeChecker_Env.try_lookup_lid
                                                            env
                                                            FStar_Parser_Const.with_type_lid
                                                           in
                                                        FStar_Option.isSome
                                                          uu____5899)
                                                      in
                                                   if uu____5896
                                                   then
                                                     let e1' =
                                                       let uu____5924 =
                                                         FStar_Options.vcgen_decorate_with_type
                                                           ()
                                                          in
                                                       if uu____5924
                                                       then
                                                         FStar_Syntax_Util.mk_with_type
                                                           u_res_t1 res_t1 e1
                                                       else e1  in
                                                     (debug1
                                                        (fun uu____5936  ->
                                                           let uu____5937 =
                                                             FStar_TypeChecker_Normalize.term_to_string
                                                               env e1'
                                                              in
                                                           let uu____5939 =
                                                             FStar_Syntax_Print.bv_to_string
                                                               x
                                                              in
                                                           FStar_Util.print2
                                                             "(3) bind (case b): Substituting %s for %s"
                                                             uu____5937
                                                             uu____5939);
                                                      (let c21 =
                                                         FStar_Syntax_Subst.subst_comp
                                                           [FStar_Syntax_Syntax.NT
                                                              (x, e1')] c2
                                                          in
                                                       mk_seq c1 b c21))
                                                   else
                                                     (debug1
                                                        (fun uu____5954  ->
                                                           let uu____5955 =
                                                             FStar_TypeChecker_Normalize.term_to_string
                                                               env e1
                                                              in
                                                           let uu____5957 =
                                                             FStar_Syntax_Print.bv_to_string
                                                               x
                                                              in
                                                           FStar_Util.print2
                                                             "(3) bind (case c): Adding equality %s = %s"
                                                             uu____5955
                                                             uu____5957);
                                                      (let c21 =
                                                         FStar_Syntax_Subst.subst_comp
                                                           [FStar_Syntax_Syntax.NT
                                                              (x, e1)] c2
                                                          in
                                                       let x_eq_e =
                                                         let uu____5964 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_Syntax_Util.mk_eq2
                                                           u_res_t1 res_t1 e1
                                                           uu____5964
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
      | uu____5982 -> g2
  
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
            (let uu____6006 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____6006)
           in
        let flags =
          if should_return1
          then
            let uu____6014 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____6014
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____6032 =
          let uu____6033 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____6033 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____6046 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____6046
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____6054 =
                  let uu____6056 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____6056  in
                (if uu____6054
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___758_6065 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___758_6065.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___758_6065.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___758_6065.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____6066 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____6066, g_c)
                 else
                   (let uu____6069 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____6069, g_c)))
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
                   let uu____6080 =
                     let uu____6081 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____6081
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____6080
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____6084 =
                   let uu____6089 =
                     let uu____6090 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____6090
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____6089  in
                 match uu____6084 with
                 | (bind_c,g_bind) ->
                     let uu____6099 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____6100 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____6099, uu____6100))
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
            fun uu____6136  ->
              match uu____6136 with
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
                    let uu____6148 =
                      ((let uu____6152 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____6152) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____6148
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6170 =
        let uu____6171 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6171  in
      FStar_Syntax_Syntax.fvar uu____6170 FStar_Syntax_Syntax.delta_constant
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
               fun uu____6241  ->
                 match uu____6241 with
                 | (uu____6255,eff_label,uu____6257,uu____6258) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____6271 =
          let uu____6279 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____6317  ->
                    match uu____6317 with
                    | (uu____6332,uu____6333,flags,uu____6335) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_6352  ->
                                match uu___5_6352 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____6355 -> false))))
             in
          if uu____6279
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____6271 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____6392 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____6394 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____6394
              then
                let uu____6401 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                   in
                (uu____6401, FStar_TypeChecker_Env.trivial_guard)
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____6440 =
                     FStar_Syntax_Util.get_match_with_close_wps
                       md.FStar_Syntax_Syntax.match_wps
                      in
                   match uu____6440 with
                   | (if_then_else1,uu____6450,uu____6451) ->
                       let uu____6452 =
                         FStar_Range.union_ranges
                           wp_t.FStar_Syntax_Syntax.pos
                           wp_e.FStar_Syntax_Syntax.pos
                          in
                       let uu____6453 =
                         let uu____6458 =
                           FStar_TypeChecker_Env.inst_effect_fun_with
                             [u_res_t] env md if_then_else1
                            in
                         let uu____6459 =
                           let uu____6460 = FStar_Syntax_Syntax.as_arg res_t1
                              in
                           let uu____6469 =
                             let uu____6480 = FStar_Syntax_Syntax.as_arg g
                                in
                             let uu____6489 =
                               let uu____6500 =
                                 FStar_Syntax_Syntax.as_arg wp_t  in
                               let uu____6509 =
                                 let uu____6520 =
                                   FStar_Syntax_Syntax.as_arg wp_e  in
                                 [uu____6520]  in
                               uu____6500 :: uu____6509  in
                             uu____6480 :: uu____6489  in
                           uu____6460 :: uu____6469  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____6458 uu____6459
                          in
                       uu____6453 FStar_Pervasives_Native.None uu____6452
                    in
                 let default_case =
                   let post_k =
                     let uu____6573 =
                       let uu____6582 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____6582]  in
                     let uu____6601 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6573 uu____6601  in
                   let kwp =
                     let uu____6607 =
                       let uu____6616 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____6616]  in
                     let uu____6635 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6607 uu____6635  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____6642 =
                       let uu____6643 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____6643]  in
                     let uu____6662 =
                       let uu____6665 =
                         let uu____6672 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____6672
                          in
                       let uu____6673 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____6665 uu____6673  in
                     FStar_Syntax_Util.abs uu____6642 uu____6662
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
                   let uu____6697 =
                     should_not_inline_whole_match ||
                       (let uu____6700 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____6700)
                      in
                   if uu____6697 then cthen true else cthen false  in
                 let uu____6707 =
                   FStar_List.fold_right
                     (fun uu____6754  ->
                        fun uu____6755  ->
                          match (uu____6754, uu____6755) with
                          | ((g,eff_label,uu____6797,cthen),(celse,g_comp))
                              ->
                              let uu____6831 =
                                let uu____6836 = maybe_return eff_label cthen
                                   in
                                FStar_TypeChecker_Common.lcomp_comp
                                  uu____6836
                                 in
                              (match uu____6831 with
                               | (cthen1,gthen) ->
                                   let uu____6843 =
                                     lift_and_destruct env cthen1 celse  in
                                   (match uu____6843 with
                                    | ((md,uu____6875,uu____6876),(uu____6877,uu____6878,wp_then),
                                       (uu____6880,uu____6881,wp_else),g_lift)
                                        ->
                                        let uu____6902 =
                                          let uu____6903 =
                                            ifthenelse md res_t g wp_then
                                              wp_else
                                             in
                                          mk_comp md u_res_t res_t uu____6903
                                            []
                                           in
                                        let uu____6904 =
                                          let uu____6905 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_comp gthen
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            uu____6905 g_lift
                                           in
                                        (uu____6902, uu____6904)))) lcases
                     (default_case, FStar_TypeChecker_Env.trivial_guard)
                    in
                 match uu____6707 with
                 | (comp,g_comp) ->
                     (match lcases with
                      | [] -> (comp, g_comp)
                      | uu____6930::[] -> (comp, g_comp)
                      | uu____6973 ->
                          let comp1 =
                            FStar_TypeChecker_Env.comp_to_comp_typ env comp
                             in
                          let md =
                            FStar_TypeChecker_Env.get_effect_decl env
                              comp1.FStar_Syntax_Syntax.effect_name
                             in
                          let uu____6992 = destruct_comp comp1  in
                          (match uu____6992 with
                           | (uu____7003,uu____7004,wp) ->
                               let uu____7006 =
                                 FStar_Syntax_Util.get_match_with_close_wps
                                   md.FStar_Syntax_Syntax.match_wps
                                  in
                               (match uu____7006 with
                                | (uu____7017,ite_wp,uu____7019) ->
                                    let wp1 =
                                      let uu____7023 =
                                        let uu____7028 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [u_res_t] env md ite_wp
                                           in
                                        let uu____7029 =
                                          let uu____7030 =
                                            FStar_Syntax_Syntax.as_arg res_t
                                             in
                                          let uu____7039 =
                                            let uu____7050 =
                                              FStar_Syntax_Syntax.as_arg wp
                                               in
                                            [uu____7050]  in
                                          uu____7030 :: uu____7039  in
                                        FStar_Syntax_Syntax.mk_Tm_app
                                          uu____7028 uu____7029
                                         in
                                      uu____7023 FStar_Pervasives_Native.None
                                        wp.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____7083 =
                                      mk_comp md u_res_t res_t wp1
                                        bind_cases_flags
                                       in
                                    (uu____7083, g_comp)))))
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
          let uu____7117 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____7117 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____7133 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____7139 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____7133 uu____7139
              else
                (let uu____7148 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____7154 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____7148 uu____7154)
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
          let uu____7179 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____7179
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____7182 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____7182
        then u_res
        else
          (let is_total =
             let uu____7189 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____7189
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____7200 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____7200 with
              | FStar_Pervasives_Native.None  ->
                  let uu____7203 =
                    let uu____7209 =
                      let uu____7211 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____7211
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____7209)
                     in
                  FStar_Errors.raise_error uu____7203
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
      let uu____7235 = destruct_comp ct  in
      match uu____7235 with
      | (u_t,t,wp) ->
          let vc =
            let uu____7254 = FStar_TypeChecker_Env.get_range env  in
            let uu____7255 =
              let uu____7260 =
                let uu____7261 =
                  FStar_All.pipe_right md.FStar_Syntax_Syntax.trivial
                    FStar_Util.must
                   in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____7261
                 in
              let uu____7264 =
                let uu____7265 = FStar_Syntax_Syntax.as_arg t  in
                let uu____7274 =
                  let uu____7285 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____7285]  in
                uu____7265 :: uu____7274  in
              FStar_Syntax_Syntax.mk_Tm_app uu____7260 uu____7264  in
            uu____7255 FStar_Pervasives_Native.None uu____7254  in
          let uu____7318 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____7318)
  
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
               let uu____7359 =
                 let uu____7360 = FStar_Syntax_Subst.compress t2  in
                 uu____7360.FStar_Syntax_Syntax.n  in
               match uu____7359 with
               | FStar_Syntax_Syntax.Tm_type uu____7364 -> true
               | uu____7366 -> false  in
             let uu____7368 =
               let uu____7369 =
                 FStar_Syntax_Util.unrefine
                   lc.FStar_TypeChecker_Common.res_typ
                  in
               uu____7369.FStar_Syntax_Syntax.n  in
             match uu____7368 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____7377 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____7387 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____7387
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____7390 =
                     let uu____7391 =
                       let uu____7392 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____7392
                        in
                     (FStar_Pervasives_Native.None, uu____7391)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____7390
                    in
                 let e1 =
                   let uu____7398 =
                     let uu____7403 =
                       let uu____7404 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____7404]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____7403  in
                   uu____7398 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____7429 -> (e, lc))
  
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
          (let uu____7464 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____7464
           then
             let uu____7467 = FStar_Syntax_Print.term_to_string e  in
             let uu____7469 = FStar_TypeChecker_Common.lcomp_to_string lc  in
             let uu____7471 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____7467 uu____7469 uu____7471
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____7481 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____7481 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____7506 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____7532 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____7532, false)
             else
               (let uu____7542 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____7542, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____7555) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____7567 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____7567
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___942_7583 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___942_7583.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___942_7583.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___942_7583.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____7590 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____7590 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____7606 =
                      let uu____7607 = FStar_TypeChecker_Common.lcomp_comp lc
                         in
                      match uu____7607 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____7627 =
                            let uu____7629 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____7629 = FStar_Syntax_Util.Equal  in
                          if uu____7627
                          then
                            ((let uu____7636 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____7636
                              then
                                let uu____7640 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____7642 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____7640 uu____7642
                              else ());
                             (let uu____7647 = set_result_typ1 c  in
                              (uu____7647, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____7654 ->
                                   true
                               | uu____7662 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____7671 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____7671
                                  in
                               let lc1 =
                                 let uu____7673 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____7674 =
                                   let uu____7675 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____7675)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____7673 uu____7674
                                  in
                               ((let uu____7679 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____7679
                                 then
                                   let uu____7683 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____7685 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____7687 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____7689 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____7683 uu____7685 uu____7687
                                     uu____7689
                                 else ());
                                (let uu____7694 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____7694 with
                                 | (c1,g_lc) ->
                                     let uu____7705 = set_result_typ1 c1  in
                                     let uu____7706 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____7705, uu____7706)))
                             else
                               ((let uu____7710 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____7710
                                 then
                                   let uu____7714 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____7716 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____7714 uu____7716
                                 else ());
                                (let uu____7721 = set_result_typ1 c  in
                                 (uu____7721, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___979_7725 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___979_7725.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___979_7725.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___979_7725.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____7735 =
                      let uu____7736 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____7736
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____7746 =
                           let uu____7747 = FStar_Syntax_Subst.compress f1
                              in
                           uu____7747.FStar_Syntax_Syntax.n  in
                         match uu____7746 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____7754,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____7756;
                                           FStar_Syntax_Syntax.vars =
                                             uu____7757;_},uu____7758)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___995_7784 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___995_7784.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___995_7784.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___995_7784.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____7785 ->
                             let uu____7786 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____7786 with
                              | (c,g_c) ->
                                  ((let uu____7798 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____7798
                                    then
                                      let uu____7802 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____7804 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____7806 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____7808 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____7802 uu____7804 uu____7806
                                        uu____7808
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
                                        let uu____7821 =
                                          let uu____7826 =
                                            let uu____7827 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____7827]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____7826
                                           in
                                        uu____7821
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____7854 =
                                      let uu____7859 =
                                        FStar_All.pipe_left
                                          (fun _7880  ->
                                             FStar_Pervasives_Native.Some
                                               _7880)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____7881 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____7882 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____7883 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____7859
                                        uu____7881 e uu____7882 uu____7883
                                       in
                                    match uu____7854 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1013_7891 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1013_7891.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1013_7891.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____7893 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____7893
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____7896 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____7896 with
                                         | (c2,g_lc) ->
                                             ((let uu____7908 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____7908
                                               then
                                                 let uu____7912 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____7912
                                               else ());
                                              (let uu____7917 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____7917))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_7926  ->
                              match uu___6_7926 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____7929 -> []))
                       in
                    let lc1 =
                      let uu____7931 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____7931 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1029_7933 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1029_7933.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1029_7933.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1029_7933.FStar_TypeChecker_Common.implicits)
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
        let uu____7969 =
          let uu____7972 =
            let uu____7977 =
              let uu____7978 =
                let uu____7987 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____7987  in
              [uu____7978]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____7977  in
          uu____7972 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____7969  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____8010 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____8010
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____8029 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____8045 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____8062 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____8062
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____8078)::(ens,uu____8080)::uu____8081 ->
                    let uu____8124 =
                      let uu____8127 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____8127  in
                    let uu____8128 =
                      let uu____8129 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____8129  in
                    (uu____8124, uu____8128)
                | uu____8132 ->
                    let uu____8143 =
                      let uu____8149 =
                        let uu____8151 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____8151
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____8149)
                       in
                    FStar_Errors.raise_error uu____8143
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____8171)::uu____8172 ->
                    let uu____8199 =
                      let uu____8204 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____8204
                       in
                    (match uu____8199 with
                     | (us_r,uu____8236) ->
                         let uu____8237 =
                           let uu____8242 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____8242
                            in
                         (match uu____8237 with
                          | (us_e,uu____8274) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____8277 =
                                  let uu____8278 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8278
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8277
                                  us_r
                                 in
                              let as_ens =
                                let uu____8280 =
                                  let uu____8281 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8281
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8280
                                  us_e
                                 in
                              let req =
                                let uu____8285 =
                                  let uu____8290 =
                                    let uu____8291 =
                                      let uu____8302 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8302]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8291
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____8290
                                   in
                                uu____8285 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____8342 =
                                  let uu____8347 =
                                    let uu____8348 =
                                      let uu____8359 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8359]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8348
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____8347
                                   in
                                uu____8342 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____8396 =
                                let uu____8399 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____8399  in
                              let uu____8400 =
                                let uu____8401 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____8401  in
                              (uu____8396, uu____8400)))
                | uu____8404 -> failwith "Impossible"))
  
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
      (let uu____8438 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____8438
       then
         let uu____8443 = FStar_Syntax_Print.term_to_string tm  in
         let uu____8445 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____8443 uu____8445
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
        (let uu____8499 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____8499
         then
           let uu____8504 = FStar_Syntax_Print.term_to_string tm  in
           let uu____8506 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____8504
             uu____8506
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____8517 =
      let uu____8519 =
        let uu____8520 = FStar_Syntax_Subst.compress t  in
        uu____8520.FStar_Syntax_Syntax.n  in
      match uu____8519 with
      | FStar_Syntax_Syntax.Tm_app uu____8524 -> false
      | uu____8542 -> true  in
    if uu____8517
    then t
    else
      (let uu____8547 = FStar_Syntax_Util.head_and_args t  in
       match uu____8547 with
       | (head1,args) ->
           let uu____8590 =
             let uu____8592 =
               let uu____8593 = FStar_Syntax_Subst.compress head1  in
               uu____8593.FStar_Syntax_Syntax.n  in
             match uu____8592 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____8598 -> false  in
           if uu____8590
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____8630 ->
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
          ((let uu____8677 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____8677
            then
              let uu____8680 = FStar_Syntax_Print.term_to_string e  in
              let uu____8682 = FStar_Syntax_Print.term_to_string t  in
              let uu____8684 =
                let uu____8686 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____8686
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____8680 uu____8682 uu____8684
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____8699 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____8699 with
              | (formals,uu____8715) ->
                  let n_implicits =
                    let uu____8737 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____8815  ->
                              match uu____8815 with
                              | (uu____8823,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____8830 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____8830 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____8737 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____8955 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____8955 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____8969 =
                      let uu____8975 =
                        let uu____8977 = FStar_Util.string_of_int n_expected
                           in
                        let uu____8979 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____8981 = FStar_Util.string_of_int n_available
                           in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____8977 uu____8979 uu____8981
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____8975)
                       in
                    let uu____8985 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____8969 uu____8985
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_9003 =
              match uu___7_9003 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____9046 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____9046 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _9177,uu____9164) when
                           _9177 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____9210,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Implicit
                                      uu____9212))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____9246 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____9246 with
                            | (v1,uu____9287,g) ->
                                ((let uu____9302 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____9302
                                  then
                                    let uu____9305 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____9305
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____9315 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____9315 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____9408 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____9408))))
                       | (uu____9435,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____9472 =
                             let uu____9485 =
                               let uu____9492 =
                                 let uu____9497 = FStar_Dyn.mkdyn env  in
                                 (uu____9497, tau)  in
                               FStar_Pervasives_Native.Some uu____9492  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____9485
                              in
                           (match uu____9472 with
                            | (v1,uu____9530,g) ->
                                ((let uu____9545 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____9545
                                  then
                                    let uu____9548 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____9548
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____9558 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____9558 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____9651 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____9651))))
                       | (uu____9678,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____9726 =
                       let uu____9753 = inst_n_binders t1  in
                       aux [] uu____9753 bs1  in
                     (match uu____9726 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____9825) -> (e, torig, guard)
                           | (uu____9856,[]) when
                               let uu____9887 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____9887 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____9889 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____9917 ->
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
            | uu____9930 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____9942 =
      let uu____9946 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____9946
        (FStar_List.map
           (fun u  ->
              let uu____9958 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____9958 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____9942 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____9986 = FStar_Util.set_is_empty x  in
      if uu____9986
      then []
      else
        (let s =
           let uu____10004 =
             let uu____10007 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____10007  in
           FStar_All.pipe_right uu____10004 FStar_Util.set_elements  in
         (let uu____10023 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____10023
          then
            let uu____10028 =
              let uu____10030 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____10030  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____10028
          else ());
         (let r =
            let uu____10039 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____10039  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____10078 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____10078
                     then
                       let uu____10083 =
                         let uu____10085 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____10085
                          in
                       let uu____10089 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____10091 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____10083 uu____10089 uu____10091
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
        let uu____10121 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____10121 FStar_Util.set_elements  in
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
        | ([],uu____10160) -> generalized_univ_names
        | (uu____10167,[]) -> explicit_univ_names
        | uu____10174 ->
            let uu____10183 =
              let uu____10189 =
                let uu____10191 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____10191
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____10189)
               in
            FStar_Errors.raise_error uu____10183 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____10213 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____10213
       then
         let uu____10218 = FStar_Syntax_Print.term_to_string t  in
         let uu____10220 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____10218 uu____10220
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____10229 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____10229
        then
          let uu____10234 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____10234
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____10243 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____10243
         then
           let uu____10248 = FStar_Syntax_Print.term_to_string t  in
           let uu____10250 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____10248 uu____10250
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
        let uu____10334 =
          let uu____10336 =
            FStar_Util.for_all
              (fun uu____10350  ->
                 match uu____10350 with
                 | (uu____10360,uu____10361,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____10336  in
        if uu____10334
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____10413 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____10413
              then
                let uu____10416 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____10416
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____10423 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____10423
               then
                 let uu____10426 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____10426
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____10444 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____10444 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____10478 =
             match uu____10478 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____10515 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____10515
                   then
                     let uu____10520 =
                       let uu____10522 =
                         let uu____10526 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____10526
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____10522
                         (FStar_String.concat ", ")
                        in
                     let uu____10574 =
                       let uu____10576 =
                         let uu____10580 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____10580
                           (FStar_List.map
                              (fun u  ->
                                 let uu____10593 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____10595 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____10593
                                   uu____10595))
                          in
                       FStar_All.pipe_right uu____10576
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____10520
                       uu____10574
                   else ());
                  (let univs2 =
                     let uu____10609 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____10621 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____10621) univs1
                       uu____10609
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____10628 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____10628
                    then
                      let uu____10633 =
                        let uu____10635 =
                          let uu____10639 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____10639
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____10635
                          (FStar_String.concat ", ")
                         in
                      let uu____10687 =
                        let uu____10689 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____10703 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____10705 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____10703
                                    uu____10705))
                           in
                        FStar_All.pipe_right uu____10689
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____10633 uu____10687
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____10726 =
             let uu____10743 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____10743  in
           match uu____10726 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____10833 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____10833
                 then ()
                 else
                   (let uu____10838 = lec_hd  in
                    match uu____10838 with
                    | (lb1,uu____10846,uu____10847) ->
                        let uu____10848 = lec2  in
                        (match uu____10848 with
                         | (lb2,uu____10856,uu____10857) ->
                             let msg =
                               let uu____10860 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10862 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____10860 uu____10862
                                in
                             let uu____10865 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____10865))
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
                 let uu____10933 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____10933
                 then ()
                 else
                   (let uu____10938 = lec_hd  in
                    match uu____10938 with
                    | (lb1,uu____10946,uu____10947) ->
                        let uu____10948 = lec2  in
                        (match uu____10948 with
                         | (lb2,uu____10956,uu____10957) ->
                             let msg =
                               let uu____10960 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10962 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____10960 uu____10962
                                in
                             let uu____10965 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____10965))
                  in
               let lecs1 =
                 let uu____10976 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____11029 = univs_and_uvars_of_lec this_lec  in
                        match uu____11029 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____10976 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____11134 = lec_hd  in
                   match uu____11134 with
                   | (lbname,e,c) ->
                       let uu____11144 =
                         let uu____11150 =
                           let uu____11152 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____11154 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____11156 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____11152 uu____11154 uu____11156
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____11150)
                          in
                       let uu____11160 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____11144 uu____11160
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____11179 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____11179 with
                         | FStar_Pervasives_Native.Some uu____11188 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____11196 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____11200 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____11200 with
                              | (bs,kres) ->
                                  ((let uu____11244 =
                                      let uu____11245 =
                                        let uu____11248 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____11248
                                         in
                                      uu____11245.FStar_Syntax_Syntax.n  in
                                    match uu____11244 with
                                    | FStar_Syntax_Syntax.Tm_type uu____11249
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____11253 =
                                          let uu____11255 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____11255  in
                                        if uu____11253
                                        then fail1 kres
                                        else ()
                                    | uu____11260 -> fail1 kres);
                                   (let a =
                                      let uu____11262 =
                                        let uu____11265 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _11268  ->
                                             FStar_Pervasives_Native.Some
                                               _11268) uu____11265
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____11262
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____11276 ->
                                          let uu____11285 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____11285
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
                      (fun uu____11388  ->
                         match uu____11388 with
                         | (lbname,e,c) ->
                             let uu____11434 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____11495 ->
                                   let uu____11508 = (e, c)  in
                                   (match uu____11508 with
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
                                                (fun uu____11548  ->
                                                   match uu____11548 with
                                                   | (x,uu____11554) ->
                                                       let uu____11555 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____11555)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____11573 =
                                                let uu____11575 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____11575
                                                 in
                                              if uu____11573
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
                                          let uu____11584 =
                                            let uu____11585 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____11585.FStar_Syntax_Syntax.n
                                             in
                                          match uu____11584 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____11610 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____11610 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____11621 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____11625 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____11625, gen_tvars))
                                in
                             (match uu____11434 with
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
        (let uu____11772 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____11772
         then
           let uu____11775 =
             let uu____11777 =
               FStar_List.map
                 (fun uu____11792  ->
                    match uu____11792 with
                    | (lb,uu____11801,uu____11802) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____11777 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____11775
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____11828  ->
                match uu____11828 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____11857 = gen env is_rec lecs  in
           match uu____11857 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____11956  ->
                       match uu____11956 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____12018 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____12018
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____12066  ->
                           match uu____12066 with
                           | (l,us,e,c,gvs) ->
                               let uu____12100 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____12102 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____12104 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____12106 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____12108 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____12100 uu____12102 uu____12104
                                 uu____12106 uu____12108))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____12153  ->
                match uu____12153 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____12197 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____12197, t, c, gvs)) univnames_lecs
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
              (let uu____12258 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____12258 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____12264 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _12267  -> FStar_Pervasives_Native.Some _12267)
                     uu____12264)
             in
          let is_var e1 =
            let uu____12275 =
              let uu____12276 = FStar_Syntax_Subst.compress e1  in
              uu____12276.FStar_Syntax_Syntax.n  in
            match uu____12275 with
            | FStar_Syntax_Syntax.Tm_name uu____12280 -> true
            | uu____12282 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1485_12303 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1485_12303.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1485_12303.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____12304 -> e2  in
          let env2 =
            let uu___1488_12306 = env1  in
            let uu____12307 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1488_12306.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1488_12306.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1488_12306.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1488_12306.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1488_12306.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1488_12306.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1488_12306.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1488_12306.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1488_12306.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1488_12306.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1488_12306.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1488_12306.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1488_12306.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1488_12306.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1488_12306.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1488_12306.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1488_12306.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____12307;
              FStar_TypeChecker_Env.is_iface =
                (uu___1488_12306.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1488_12306.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1488_12306.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1488_12306.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1488_12306.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1488_12306.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1488_12306.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1488_12306.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1488_12306.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1488_12306.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1488_12306.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1488_12306.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1488_12306.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1488_12306.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1488_12306.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1488_12306.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1488_12306.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1488_12306.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1488_12306.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1488_12306.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1488_12306.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1488_12306.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1488_12306.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1488_12306.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1488_12306.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1488_12306.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1488_12306.FStar_TypeChecker_Env.strict_args_tab)
            }  in
          let uu____12309 = check1 env2 t1 t2  in
          match uu____12309 with
          | FStar_Pervasives_Native.None  ->
              let uu____12316 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____12322 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____12316 uu____12322
          | FStar_Pervasives_Native.Some g ->
              ((let uu____12329 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12329
                then
                  let uu____12334 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____12334
                else ());
               (let uu____12340 = decorate e t2  in (uu____12340, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____12368 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____12368
         then
           let uu____12371 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____12371
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____12385 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____12385 with
         | (c,g_c) ->
             let uu____12397 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____12397
             then
               let uu____12405 =
                 let uu____12407 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____12407  in
               (uu____12405, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____12415 =
                    let uu____12416 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____12416
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____12415
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____12417 = check_trivial_precondition env c1  in
                match uu____12417 with
                | (ct,vc,g_pre) ->
                    ((let uu____12433 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____12433
                      then
                        let uu____12438 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____12438
                      else ());
                     (let uu____12443 =
                        let uu____12445 =
                          let uu____12446 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____12446  in
                        discharge uu____12445  in
                      let uu____12447 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____12443, uu____12447)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_12481 =
        match uu___8_12481 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____12491)::[] -> f fst1
        | uu____12516 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____12528 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____12528
          (fun _12529  -> FStar_TypeChecker_Common.NonTrivial _12529)
         in
      let op_or_e e =
        let uu____12540 =
          let uu____12541 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____12541  in
        FStar_All.pipe_right uu____12540
          (fun _12544  -> FStar_TypeChecker_Common.NonTrivial _12544)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _12551  -> FStar_TypeChecker_Common.NonTrivial _12551)
         in
      let op_or_t t =
        let uu____12562 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____12562
          (fun _12565  -> FStar_TypeChecker_Common.NonTrivial _12565)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _12572  -> FStar_TypeChecker_Common.NonTrivial _12572)
         in
      let short_op_ite uu___9_12578 =
        match uu___9_12578 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____12588)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____12615)::[] ->
            let uu____12656 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____12656
              (fun _12657  -> FStar_TypeChecker_Common.NonTrivial _12657)
        | uu____12658 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____12670 =
          let uu____12678 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____12678)  in
        let uu____12686 =
          let uu____12696 =
            let uu____12704 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____12704)  in
          let uu____12712 =
            let uu____12722 =
              let uu____12730 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____12730)  in
            let uu____12738 =
              let uu____12748 =
                let uu____12756 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____12756)  in
              let uu____12764 =
                let uu____12774 =
                  let uu____12782 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____12782)  in
                [uu____12774; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____12748 :: uu____12764  in
            uu____12722 :: uu____12738  in
          uu____12696 :: uu____12712  in
        uu____12670 :: uu____12686  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____12844 =
            FStar_Util.find_map table
              (fun uu____12859  ->
                 match uu____12859 with
                 | (x,mk1) ->
                     let uu____12876 = FStar_Ident.lid_equals x lid  in
                     if uu____12876
                     then
                       let uu____12881 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____12881
                     else FStar_Pervasives_Native.None)
             in
          (match uu____12844 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____12885 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____12893 =
      let uu____12894 = FStar_Syntax_Util.un_uinst l  in
      uu____12894.FStar_Syntax_Syntax.n  in
    match uu____12893 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____12899 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____12935)::uu____12936 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____12955 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____12964,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____12965))::uu____12966 -> bs
      | uu____12984 ->
          let uu____12985 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____12985 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____12989 =
                 let uu____12990 = FStar_Syntax_Subst.compress t  in
                 uu____12990.FStar_Syntax_Syntax.n  in
               (match uu____12989 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____12994) ->
                    let uu____13015 =
                      FStar_Util.prefix_until
                        (fun uu___10_13055  ->
                           match uu___10_13055 with
                           | (uu____13063,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____13064)) ->
                               false
                           | uu____13069 -> true) bs'
                       in
                    (match uu____13015 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____13105,uu____13106) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____13178,uu____13179) ->
                         let uu____13252 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____13272  ->
                                   match uu____13272 with
                                   | (x,uu____13281) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____13252
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____13330  ->
                                     match uu____13330 with
                                     | (x,i) ->
                                         let uu____13349 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____13349, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____13360 -> bs))
  
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
            let uu____13389 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____13389
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
          let uu____13420 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____13420
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
        (let uu____13463 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____13463
         then
           ((let uu____13468 = FStar_Ident.text_of_lid lident  in
             d uu____13468);
            (let uu____13470 = FStar_Ident.text_of_lid lident  in
             let uu____13472 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____13470 uu____13472))
         else ());
        (let fv =
           let uu____13478 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____13478
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
         let uu____13490 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1645_13492 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1645_13492.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1645_13492.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1645_13492.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1645_13492.FStar_Syntax_Syntax.sigattrs)
           }), uu____13490))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_13510 =
        match uu___11_13510 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____13513 -> false  in
      let reducibility uu___12_13521 =
        match uu___12_13521 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____13528 -> false  in
      let assumption uu___13_13536 =
        match uu___13_13536 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____13540 -> false  in
      let reification uu___14_13548 =
        match uu___14_13548 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____13551 -> true
        | uu____13553 -> false  in
      let inferred uu___15_13561 =
        match uu___15_13561 with
        | FStar_Syntax_Syntax.Discriminator uu____13563 -> true
        | FStar_Syntax_Syntax.Projector uu____13565 -> true
        | FStar_Syntax_Syntax.RecordType uu____13571 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____13581 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____13594 -> false  in
      let has_eq uu___16_13602 =
        match uu___16_13602 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____13606 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____13685 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____13692 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____13703 =
        let uu____13705 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___17_13711  ->
                  match uu___17_13711 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____13714 -> false))
           in
        FStar_All.pipe_right uu____13705 Prims.op_Negation  in
      if uu____13703
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____13735 =
            let uu____13741 =
              let uu____13743 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____13743 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____13741)  in
          FStar_Errors.raise_error uu____13735 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____13761 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____13769 =
            let uu____13771 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____13771  in
          if uu____13769 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____13781),uu____13782) ->
              ((let uu____13794 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____13794
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____13803 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____13803
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____13814 ->
              let uu____13823 =
                let uu____13825 =
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
                Prims.op_Negation uu____13825  in
              if uu____13823 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____13835 ->
              let uu____13842 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____13842 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____13850 ->
              let uu____13857 =
                let uu____13859 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____13859  in
              if uu____13857 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____13869 ->
              let uu____13870 =
                let uu____13872 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____13872  in
              if uu____13870 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13882 ->
              let uu____13883 =
                let uu____13885 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____13885  in
              if uu____13883 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13895 ->
              let uu____13908 =
                let uu____13910 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____13910  in
              if uu____13908 then err'1 () else ()
          | uu____13920 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let has_erased_for_extraction_attr fv =
        let uu____13943 =
          let uu____13948 =
            FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
          FStar_All.pipe_right uu____13948
            (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
           in
        FStar_All.pipe_right uu____13943
          (fun l_opt  ->
             (FStar_Util.is_some l_opt) &&
               (let uu____13967 = FStar_All.pipe_right l_opt FStar_Util.must
                   in
                FStar_All.pipe_right uu____13967
                  (FStar_List.existsb
                     (fun t1  ->
                        let uu____13985 =
                          let uu____13986 = FStar_Syntax_Subst.compress t1
                             in
                          uu____13986.FStar_Syntax_Syntax.n  in
                        match uu____13985 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            FStar_Ident.lid_equals
                              (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              FStar_Parser_Const.must_erase_for_extraction_attr
                            -> true
                        | uu____13992 -> false))))
         in
      let rec aux_whnf env t1 =
        let uu____14018 =
          let uu____14019 = FStar_Syntax_Subst.compress t1  in
          uu____14019.FStar_Syntax_Syntax.n  in
        match uu____14018 with
        | FStar_Syntax_Syntax.Tm_type uu____14023 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (has_erased_for_extraction_attr fv)
        | FStar_Syntax_Syntax.Tm_arrow uu____14026 ->
            let uu____14041 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____14041 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____14074 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____14074
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____14080;
               FStar_Syntax_Syntax.index = uu____14081;
               FStar_Syntax_Syntax.sort = t2;_},uu____14083)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14092,uu____14093) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____14135::[]) ->
            let uu____14174 =
              let uu____14175 = FStar_Syntax_Util.un_uinst head1  in
              uu____14175.FStar_Syntax_Syntax.n  in
            (match uu____14174 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.erased_lid)
                   || (has_erased_for_extraction_attr fv)
             | uu____14180 -> false)
        | uu____14182 -> false
      
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
        (let uu____14192 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____14192
         then
           let uu____14197 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____14197
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
              let uu____14244 =
                let uu____14245 = FStar_Syntax_Subst.compress signature  in
                uu____14245.FStar_Syntax_Syntax.n  in
              match uu____14244 with
              | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14249) when
                  (FStar_List.length bs) = (Prims.of_int (2)) ->
                  let uu____14278 = FStar_Syntax_Subst.open_binders bs  in
                  (match uu____14278 with
                   | (a,uu____14280)::(wp,uu____14282)::[] ->
                       FStar_All.pipe_right wp.FStar_Syntax_Syntax.sort
                         (FStar_Syntax_Subst.subst
                            [FStar_Syntax_Syntax.NT (a, a_tm)]))
              | uu____14311 ->
                  let uu____14312 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name signature
                     in
                  FStar_Errors.raise_error uu____14312 r
               in
            let uu____14318 =
              let uu____14331 =
                let uu____14333 = FStar_Range.string_of_range r  in
                FStar_Util.format2 "implicit for wp of %s at %s"
                  eff_name.FStar_Ident.str uu____14333
                 in
              new_implicit_var uu____14331 r env wp_sort  in
            match uu____14318 with
            | (wp_uvar,uu____14341,g_wp_uvar) ->
                let eff_c =
                  let uu____14356 =
                    let uu____14357 =
                      let uu____14368 =
                        FStar_All.pipe_right wp_uvar
                          FStar_Syntax_Syntax.as_arg
                         in
                      [uu____14368]  in
                    {
                      FStar_Syntax_Syntax.comp_univs = [u];
                      FStar_Syntax_Syntax.effect_name = eff_name;
                      FStar_Syntax_Syntax.result_typ = a_tm;
                      FStar_Syntax_Syntax.effect_args = uu____14357;
                      FStar_Syntax_Syntax.flags = []
                    }  in
                  FStar_Syntax_Syntax.mk_Comp uu____14356  in
                let uu____14401 =
                  let uu____14402 =
                    let uu____14409 =
                      let uu____14410 =
                        let uu____14425 =
                          let uu____14434 =
                            FStar_Syntax_Syntax.null_binder
                              FStar_Syntax_Syntax.t_unit
                             in
                          [uu____14434]  in
                        (uu____14425, eff_c)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____14410  in
                    FStar_Syntax_Syntax.mk uu____14409  in
                  uu____14402 FStar_Pervasives_Native.None r  in
                (uu____14401, g_wp_uvar)
  
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
                  let uu____14513 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____14513 r  in
                let uu____14523 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____14523 with
                | (uu____14532,signature) ->
                    let uu____14534 =
                      let uu____14535 = FStar_Syntax_Subst.compress signature
                         in
                      uu____14535.FStar_Syntax_Syntax.n  in
                    (match uu____14534 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14543) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____14591 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____14606 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____14608 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____14606 eff_name.FStar_Ident.str
                                       uu____14608) r
                                 in
                              (match uu____14591 with
                               | (is,g) ->
                                   let repr =
                                     let uu____14622 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts [u]
                                        in
                                     FStar_All.pipe_right uu____14622
                                       FStar_Pervasives_Native.snd
                                      in
                                   let uu____14631 =
                                     let uu____14632 =
                                       let uu____14637 =
                                         FStar_List.map
                                           FStar_Syntax_Syntax.as_arg (a_tm
                                           :: is)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr
                                         uu____14637
                                        in
                                     uu____14632 FStar_Pervasives_Native.None
                                       r
                                      in
                                   (uu____14631, g))
                          | uu____14646 -> fail1 signature)
                     | uu____14647 -> fail1 signature)
  
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
            let uu____14678 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____14678
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
              let uu____14723 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____14723 with
              | (uu____14728,sig_tm) ->
                  let fail1 t =
                    let uu____14736 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____14736 r  in
                  let uu____14742 =
                    let uu____14743 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____14743.FStar_Syntax_Syntax.n  in
                  (match uu____14742 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14747) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____14770)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____14792 -> fail1 sig_tm)
                   | uu____14793 -> fail1 sig_tm)
  
let (lift_tf_layered_effect :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.tscheme -> FStar_TypeChecker_Env.lift_comp_t)
  =
  fun tgt  ->
    fun lift_ts  ->
      fun env  ->
        fun c  ->
          (let uu____14814 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____14814
           then
             let uu____14819 = FStar_Syntax_Print.comp_to_string c  in
             let uu____14821 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____14819 uu____14821
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let effect_args_from_repr repr is_layered =
             let err uu____14851 =
               let uu____14852 =
                 let uu____14858 =
                   let uu____14860 = FStar_Syntax_Print.term_to_string repr
                      in
                   let uu____14862 = FStar_Util.string_of_bool is_layered  in
                   FStar_Util.format2
                     "Could not get effect args from repr %s with is_layered %s"
                     uu____14860 uu____14862
                    in
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____14858)  in
               FStar_Errors.raise_error uu____14852 r  in
             let repr1 = FStar_Syntax_Subst.compress repr  in
             if is_layered
             then
               match repr1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_app (uu____14874,uu____14875::is) ->
                   FStar_All.pipe_right is
                     (FStar_List.map FStar_Pervasives_Native.fst)
               | uu____14943 -> err ()
             else
               (match repr1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (uu____14948,c1) ->
                    let uu____14970 =
                      FStar_All.pipe_right c1
                        FStar_Syntax_Util.comp_to_comp_typ
                       in
                    FStar_All.pipe_right uu____14970
                      (fun ct  ->
                         FStar_All.pipe_right
                           ct.FStar_Syntax_Syntax.effect_args
                           (FStar_List.map FStar_Pervasives_Native.fst))
                | uu____15005 -> err ())
              in
           let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____15007 =
             let uu____15018 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____15019 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____15018, (ct.FStar_Syntax_Syntax.result_typ), uu____15019)
              in
           match uu____15007 with
           | (u,a,c_is) ->
               let uu____15067 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____15067 with
                | (uu____15076,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____15087 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____15089 = FStar_Ident.string_of_lid tgt  in
                      let uu____15091 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____15087 uu____15089 s uu____15091
                       in
                    let uu____15094 =
                      let uu____15127 =
                        let uu____15128 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____15128.FStar_Syntax_Syntax.n  in
                      match uu____15127 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____15192 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____15192 with
                           | (a_b::bs1,c2) ->
                               let uu____15252 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               let uu____15314 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____15252, uu____15314))
                      | uu____15341 ->
                          let uu____15342 =
                            let uu____15348 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____15348)
                             in
                          FStar_Errors.raise_error uu____15342 r
                       in
                    (match uu____15094 with
                     | (a_b,(rest_bs,f_b::[]),lift_ct) ->
                         let uu____15466 =
                           let uu____15473 =
                             let uu____15474 =
                               let uu____15475 =
                                 let uu____15482 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____15482, a)  in
                               FStar_Syntax_Syntax.NT uu____15475  in
                             [uu____15474]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____15473
                             (fun b  ->
                                let uu____15499 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____15501 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____15503 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____15505 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____15499 uu____15501 uu____15503
                                  uu____15505) r
                            in
                         (match uu____15466 with
                          | (rest_bs_uvars,g) ->
                              let substs =
                                FStar_List.map2
                                  (fun b  ->
                                     fun t  ->
                                       let uu____15542 =
                                         let uu____15549 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____15549, t)  in
                                       FStar_Syntax_Syntax.NT uu____15542)
                                  (a_b :: rest_bs) (a :: rest_bs_uvars)
                                 in
                              let guard_f =
                                let f_sort =
                                  let uu____15568 =
                                    FStar_All.pipe_right
                                      (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                      (FStar_Syntax_Subst.subst substs)
                                     in
                                  FStar_All.pipe_right uu____15568
                                    FStar_Syntax_Subst.compress
                                   in
                                let f_sort_is =
                                  let uu____15574 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env ct.FStar_Syntax_Syntax.effect_name
                                     in
                                  effect_args_from_repr f_sort uu____15574
                                   in
                                FStar_List.fold_left2
                                  (fun g1  ->
                                     fun i1  ->
                                       fun i2  ->
                                         let uu____15583 =
                                           FStar_TypeChecker_Rel.teq env i1
                                             i2
                                            in
                                         FStar_TypeChecker_Env.conj_guard g1
                                           uu____15583)
                                  FStar_TypeChecker_Env.trivial_guard c_is
                                  f_sort_is
                                 in
                              let is =
                                let uu____15587 =
                                  FStar_TypeChecker_Env.is_layered_effect env
                                    tgt
                                   in
                                effect_args_from_repr
                                  lift_ct.FStar_Syntax_Syntax.result_typ
                                  uu____15587
                                 in
                              let c1 =
                                let uu____15590 =
                                  let uu____15591 =
                                    let uu____15602 =
                                      FStar_All.pipe_right is
                                        (FStar_List.map
                                           (FStar_Syntax_Subst.subst substs))
                                       in
                                    FStar_All.pipe_right uu____15602
                                      (FStar_List.map
                                         FStar_Syntax_Syntax.as_arg)
                                     in
                                  {
                                    FStar_Syntax_Syntax.comp_univs =
                                      (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                    FStar_Syntax_Syntax.effect_name = tgt;
                                    FStar_Syntax_Syntax.result_typ = a;
                                    FStar_Syntax_Syntax.effect_args =
                                      uu____15591;
                                    FStar_Syntax_Syntax.flags =
                                      (ct.FStar_Syntax_Syntax.flags)
                                  }  in
                                FStar_Syntax_Syntax.mk_Comp uu____15590  in
                              ((let uu____15622 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____15622
                                then
                                  let uu____15627 =
                                    FStar_Syntax_Print.comp_to_string c1  in
                                  FStar_Util.print1 "} Lifted comp: %s\n"
                                    uu____15627
                                else ());
                               (let uu____15632 =
                                  FStar_TypeChecker_Env.conj_guard g guard_f
                                   in
                                (c1, uu____15632)))))))
  