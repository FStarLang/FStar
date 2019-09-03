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
  
let (mk_layered_bind :
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
              (let uu____2308 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "LayeredEffects")
                  in
               if uu____2308
               then
                 let uu____2313 = FStar_Syntax_Print.comp_to_string c1  in
                 let uu____2315 = FStar_Syntax_Print.comp_to_string c2  in
                 FStar_Util.print2 "Binding c1:%s and c2:%s {\n" uu____2313
                   uu____2315
               else ());
              (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1
                  in
               let ct2 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2
                  in
               let x_a =
                 match b with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Syntax_Syntax.null_binder
                       ct1.FStar_Syntax_Syntax.result_typ
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Syntax.mk_binder x
                  in
               let uu____2336 =
                 let c1_ed =
                   FStar_TypeChecker_Env.get_effect_decl env
                     ct1.FStar_Syntax_Syntax.effect_name
                    in
                 let c2_ed =
                   FStar_TypeChecker_Env.get_effect_decl env
                     ct2.FStar_Syntax_Syntax.effect_name
                    in
                 let uu____2347 =
                   FStar_TypeChecker_Env.monad_leq env
                     c1_ed.FStar_Syntax_Syntax.mname
                     c2_ed.FStar_Syntax_Syntax.mname
                    in
                 match uu____2347 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____2358 =
                       FStar_TypeChecker_Env.monad_leq env
                         c2_ed.FStar_Syntax_Syntax.mname
                         c1_ed.FStar_Syntax_Syntax.mname
                        in
                     (match uu____2358 with
                      | FStar_Pervasives_Native.None  ->
                          let uu____2369 =
                            let uu____2375 =
                              FStar_Util.format2
                                "Effects %s and %s cannot be composed"
                                (c1_ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                (c2_ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                               in
                            (FStar_Errors.Fatal_EffectsCannotBeComposed,
                              uu____2375)
                             in
                          FStar_Errors.raise_error uu____2369 r1
                      | FStar_Pervasives_Native.Some edge ->
                          let env_l =
                            FStar_TypeChecker_Env.push_binders env [x_a]  in
                          let uu____2401 =
                            let uu____2406 =
                              let uu____2411 =
                                FStar_All.pipe_right ct2
                                  FStar_Syntax_Syntax.mk_Comp
                                 in
                              FStar_All.pipe_right uu____2411
                                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                   env_l)
                               in
                            FStar_All.pipe_right uu____2406
                              (fun uu____2428  ->
                                 match uu____2428 with
                                 | (c,g) ->
                                     let uu____2439 =
                                       FStar_Syntax_Util.comp_to_comp_typ c
                                        in
                                     (uu____2439, g))
                             in
                          (match uu____2401 with
                           | (ct21,g_lift) ->
                               let uu____2450 =
                                 FStar_TypeChecker_Env.close_guard env 
                                   [x_a] g_lift
                                  in
                               (ct1, ct21, c1_ed, uu____2450)))
                 | FStar_Pervasives_Native.Some edge ->
                     let uu____2464 =
                       let uu____2469 =
                         let uu____2474 =
                           FStar_All.pipe_right ct1
                             FStar_Syntax_Syntax.mk_Comp
                            in
                         FStar_All.pipe_right uu____2474
                           ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                              env)
                          in
                       FStar_All.pipe_right uu____2469
                         (fun uu____2491  ->
                            match uu____2491 with
                            | (c,g) ->
                                let uu____2502 =
                                  FStar_Syntax_Util.comp_to_comp_typ c  in
                                (uu____2502, g))
                        in
                     (match uu____2464 with
                      | (ct11,g_lift) -> (ct11, ct2, c2_ed, g_lift))
                  in
               match uu____2336 with
               | (ct11,ct21,ed,g_lift) ->
                   ((let uu____2522 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "LayeredEffects")
                        in
                     if uu____2522
                     then
                       let uu____2527 =
                         let uu____2529 =
                           FStar_All.pipe_right ct11
                             FStar_Syntax_Syntax.mk_Comp
                            in
                         FStar_All.pipe_right uu____2529
                           FStar_Syntax_Print.comp_to_string
                          in
                       let uu____2531 =
                         let uu____2533 =
                           FStar_All.pipe_right ct21
                             FStar_Syntax_Syntax.mk_Comp
                            in
                         FStar_All.pipe_right uu____2533
                           FStar_Syntax_Print.comp_to_string
                          in
                       FStar_Util.print2
                         "After lifting, ct1: %s and ct2: %s\n" uu____2527
                         uu____2531
                     else ());
                    (let uu____2538 =
                       let uu____2549 =
                         FStar_List.hd ct11.FStar_Syntax_Syntax.comp_univs
                          in
                       let uu____2550 =
                         FStar_List.map FStar_Pervasives_Native.fst
                           ct11.FStar_Syntax_Syntax.effect_args
                          in
                       (uu____2549, (ct11.FStar_Syntax_Syntax.result_typ),
                         uu____2550)
                        in
                     match uu____2538 with
                     | (u1,t1,is1) ->
                         let uu____2584 =
                           let uu____2595 =
                             FStar_List.hd
                               ct21.FStar_Syntax_Syntax.comp_univs
                              in
                           let uu____2596 =
                             FStar_List.map FStar_Pervasives_Native.fst
                               ct21.FStar_Syntax_Syntax.effect_args
                              in
                           (uu____2595,
                             (ct21.FStar_Syntax_Syntax.result_typ),
                             uu____2596)
                            in
                         (match uu____2584 with
                          | (u2,t2,is2) ->
                              let uu____2630 =
                                FStar_TypeChecker_Env.inst_tscheme_with
                                  ed.FStar_Syntax_Syntax.bind_wp [u1; u2]
                                 in
                              (match uu____2630 with
                               | (uu____2639,bind_t) ->
                                   let bind_t_shape_error s =
                                     let uu____2654 =
                                       let uu____2656 =
                                         FStar_Syntax_Print.term_to_string
                                           bind_t
                                          in
                                       FStar_Util.format2
                                         "bind %s does not have proper shape (reason:%s)"
                                         uu____2656 s
                                        in
                                     (FStar_Errors.Fatal_UnexpectedEffect,
                                       uu____2654)
                                      in
                                   let uu____2660 =
                                     let uu____2705 =
                                       let uu____2706 =
                                         FStar_Syntax_Subst.compress bind_t
                                          in
                                       uu____2706.FStar_Syntax_Syntax.n  in
                                     match uu____2705 with
                                     | FStar_Syntax_Syntax.Tm_arrow (bs,c)
                                         when
                                         (FStar_List.length bs) >=
                                           (Prims.of_int (4))
                                         ->
                                         let uu____2782 =
                                           FStar_Syntax_Subst.open_comp bs c
                                            in
                                         (match uu____2782 with
                                          | (a_b::b_b::bs1,c3) ->
                                              let uu____2867 =
                                                let uu____2894 =
                                                  FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2)))
                                                    bs1
                                                   in
                                                FStar_All.pipe_right
                                                  uu____2894
                                                  (fun uu____2979  ->
                                                     match uu____2979 with
                                                     | (l1,l2) ->
                                                         let uu____3060 =
                                                           FStar_List.hd l2
                                                            in
                                                         let uu____3073 =
                                                           let uu____3080 =
                                                             FStar_List.tl l2
                                                              in
                                                           FStar_List.hd
                                                             uu____3080
                                                            in
                                                         (l1, uu____3060,
                                                           uu____3073))
                                                 in
                                              (match uu____2867 with
                                               | (rest_bs,f_b,g_b) ->
                                                   let uu____3208 =
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                       c3
                                                      in
                                                   (a_b, b_b, rest_bs, f_b,
                                                     g_b, uu____3208)))
                                     | uu____3241 ->
                                         let uu____3242 =
                                           bind_t_shape_error
                                             "Either not an arrow or not enough binders"
                                            in
                                         FStar_Errors.raise_error uu____3242
                                           r1
                                      in
                                   (match uu____2660 with
                                    | (a_b,b_b,rest_bs,f_b,g_b,bind_ct) ->
                                        let uu____3367 =
                                          let uu____3374 =
                                            let uu____3375 =
                                              let uu____3376 =
                                                let uu____3383 =
                                                  FStar_All.pipe_right a_b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____3383, t1)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____3376
                                               in
                                            let uu____3394 =
                                              let uu____3397 =
                                                let uu____3398 =
                                                  let uu____3405 =
                                                    FStar_All.pipe_right b_b
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  (uu____3405, t2)  in
                                                FStar_Syntax_Syntax.NT
                                                  uu____3398
                                                 in
                                              [uu____3397]  in
                                            uu____3375 :: uu____3394  in
                                          FStar_TypeChecker_Env.uvars_for_binders
                                            env rest_bs uu____3374
                                            (fun b1  ->
                                               let uu____3420 =
                                                 FStar_Syntax_Print.binder_to_string
                                                   b1
                                                  in
                                               let uu____3422 =
                                                 FStar_Range.string_of_range
                                                   r1
                                                  in
                                               FStar_Util.format3
                                                 "implicit var for binder %s of %s:bind at %s"
                                                 uu____3420
                                                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                 uu____3422) r1
                                           in
                                        (match uu____3367 with
                                         | (rest_bs_uvars,g_uvars) ->
                                             let subst1 =
                                               FStar_List.map2
                                                 (fun b1  ->
                                                    fun t  ->
                                                      let uu____3459 =
                                                        let uu____3466 =
                                                          FStar_All.pipe_right
                                                            b1
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____3466, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____3459) (a_b ::
                                                 b_b :: rest_bs) (t1 :: t2 ::
                                                 rest_bs_uvars)
                                                in
                                             let f_guard =
                                               let f_sort_is =
                                                 let uu____3493 =
                                                   let uu____3494 =
                                                     let uu____3497 =
                                                       let uu____3498 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____3498.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____3497
                                                      in
                                                   uu____3494.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____3493 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____3509,uu____3510::is)
                                                     ->
                                                     let uu____3552 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3552
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             subst1))
                                                 | uu____3585 ->
                                                     let uu____3586 =
                                                       bind_t_shape_error
                                                         "f's type is not a repr type"
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____3586 r1
                                                  in
                                               FStar_List.fold_left2
                                                 (fun g  ->
                                                    fun i1  ->
                                                      fun f_i1  ->
                                                        let uu____3602 =
                                                          FStar_TypeChecker_Rel.teq
                                                            env i1 f_i1
                                                           in
                                                        FStar_TypeChecker_Env.conj_guard
                                                          g uu____3602)
                                                 FStar_TypeChecker_Env.trivial_guard
                                                 is1 f_sort_is
                                                in
                                             let g_guard =
                                               let g_sort_is =
                                                 let uu____3607 =
                                                   let uu____3608 =
                                                     let uu____3611 =
                                                       let uu____3612 =
                                                         FStar_All.pipe_right
                                                           g_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____3612.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____3611
                                                      in
                                                   uu____3608.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____3607 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____3645 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c
                                                        in
                                                     (match uu____3645 with
                                                      | (bs1,c3) ->
                                                          let bs_subst =
                                                            let uu____3655 =
                                                              let uu____3662
                                                                =
                                                                let uu____3663
                                                                  =
                                                                  FStar_List.hd
                                                                    bs1
                                                                   in
                                                                FStar_All.pipe_right
                                                                  uu____3663
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              let uu____3684
                                                                =
                                                                let uu____3687
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                   in
                                                                FStar_All.pipe_right
                                                                  uu____3687
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                 in
                                                              (uu____3662,
                                                                uu____3684)
                                                               in
                                                            FStar_Syntax_Syntax.NT
                                                              uu____3655
                                                             in
                                                          let c4 =
                                                            FStar_Syntax_Subst.subst_comp
                                                              [bs_subst] c3
                                                             in
                                                          let uu____3701 =
                                                            let uu____3702 =
                                                              FStar_Syntax_Subst.compress
                                                                (FStar_Syntax_Util.comp_result
                                                                   c4)
                                                               in
                                                            uu____3702.FStar_Syntax_Syntax.n
                                                             in
                                                          (match uu____3701
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_app
                                                               (uu____3707,uu____3708::is)
                                                               ->
                                                               let uu____3750
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   is
                                                                   (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____3750
                                                                 (FStar_List.map
                                                                    (
                                                                    FStar_Syntax_Subst.subst
                                                                    subst1))
                                                           | uu____3783 ->
                                                               let uu____3784
                                                                 =
                                                                 bind_t_shape_error
                                                                   "g's type is not a repr type"
                                                                  in
                                                               FStar_Errors.raise_error
                                                                 uu____3784
                                                                 r1))
                                                 | uu____3793 ->
                                                     let uu____3794 =
                                                       bind_t_shape_error
                                                         "g's type is not an arrow"
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____3794 r1
                                                  in
                                               let env_g =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env [x_a]
                                                  in
                                               let uu____3816 =
                                                 FStar_List.fold_left2
                                                   (fun g  ->
                                                      fun i1  ->
                                                        fun g_i1  ->
                                                          let uu____3824 =
                                                            FStar_TypeChecker_Rel.teq
                                                              env_g i1 g_i1
                                                             in
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g uu____3824)
                                                   FStar_TypeChecker_Env.trivial_guard
                                                   is2 g_sort_is
                                                  in
                                               FStar_All.pipe_right
                                                 uu____3816
                                                 (FStar_TypeChecker_Env.close_guard
                                                    env [x_a])
                                                in
                                             let is =
                                               let uu____3840 =
                                                 let uu____3841 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_ct.FStar_Syntax_Syntax.result_typ
                                                    in
                                                 uu____3841.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____3840 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____3846,uu____3847::is)
                                                   ->
                                                   let uu____3889 =
                                                     FStar_All.pipe_right is
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3889
                                                     (FStar_List.map
                                                        (FStar_Syntax_Subst.subst
                                                           subst1))
                                               | uu____3922 ->
                                                   let uu____3923 =
                                                     bind_t_shape_error
                                                       "return type is not a repr type"
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____3923 r1
                                                in
                                             let c =
                                               let uu____3933 =
                                                 let uu____3934 =
                                                   FStar_List.map
                                                     FStar_Syntax_Syntax.as_arg
                                                     is
                                                    in
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
                                                     = uu____3934;
                                                   FStar_Syntax_Syntax.flags
                                                     = flags
                                                 }  in
                                               FStar_Syntax_Syntax.mk_Comp
                                                 uu____3933
                                                in
                                             ((let uu____3954 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____3954
                                               then
                                                 let uu____3959 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c
                                                    in
                                                 FStar_Util.print1
                                                   "} c after bind: %s\n"
                                                   uu____3959
                                               else ());
                                              (let uu____3964 =
                                                 FStar_TypeChecker_Env.conj_guards
                                                   [g_lift;
                                                   g_uvars;
                                                   f_guard;
                                                   g_guard]
                                                  in
                                               (c, uu____3964))))))))))
  
let (mk_non_layered_bind :
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
              let uu____4012 = lift_and_destruct env c1 c2  in
              match uu____4012 with
              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2),g) ->
                  let bs =
                    match b with
                    | FStar_Pervasives_Native.None  ->
                        let uu____4072 = FStar_Syntax_Syntax.null_binder t1
                           in
                        [uu____4072]
                    | FStar_Pervasives_Native.Some x ->
                        let uu____4092 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4092]
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
                    let uu____4139 = FStar_Syntax_Syntax.as_arg r11  in
                    let uu____4148 =
                      let uu____4159 = FStar_Syntax_Syntax.as_arg t1  in
                      let uu____4168 =
                        let uu____4179 = FStar_Syntax_Syntax.as_arg t2  in
                        let uu____4188 =
                          let uu____4199 = FStar_Syntax_Syntax.as_arg wp1  in
                          let uu____4208 =
                            let uu____4219 =
                              let uu____4228 = mk_lam wp2  in
                              FStar_Syntax_Syntax.as_arg uu____4228  in
                            [uu____4219]  in
                          uu____4199 :: uu____4208  in
                        uu____4179 :: uu____4188  in
                      uu____4159 :: uu____4168  in
                    uu____4139 :: uu____4148  in
                  let wp =
                    let uu____4280 =
                      let uu____4285 =
                        FStar_TypeChecker_Env.inst_effect_fun_with
                          [u_t1; u_t2] env md md.FStar_Syntax_Syntax.bind_wp
                         in
                      FStar_Syntax_Syntax.mk_Tm_app uu____4285 wp_args  in
                    uu____4280 FStar_Pervasives_Native.None
                      t2.FStar_Syntax_Syntax.pos
                     in
                  let uu____4286 = mk_comp md u_t2 t2 wp flags  in
                  (uu____4286, g)
  
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
              let bind_f =
                let uu____4367 =
                  let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1
                     in
                  let ct2 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2
                     in
                  (FStar_TypeChecker_Env.is_layered_effect env
                     ct1.FStar_Syntax_Syntax.effect_name)
                    ||
                    (FStar_TypeChecker_Env.is_layered_effect env
                       ct2.FStar_Syntax_Syntax.effect_name)
                   in
                if uu____4367 then mk_layered_bind else mk_non_layered_bind
                 in
              bind_f env c1 b c2 flags r1
  
let (lift_wp_and_bind_with :
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
          let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
          let edge =
            let uu____4436 =
              FStar_TypeChecker_Env.monad_leq env
                FStar_Parser_Const.effect_PURE_lid
                ct.FStar_Syntax_Syntax.effect_name
               in
            match uu____4436 with
            | FStar_Pervasives_Native.Some edge -> edge
            | FStar_Pervasives_Native.None  ->
                failwith
                  (Prims.op_Hat
                     "Impossible! lift_wp_and_bind_with: did not find a lift from PURE to "
                     (ct.FStar_Syntax_Syntax.effect_name).FStar_Ident.str)
             in
          let pure_c =
            let uu____4442 =
              let uu____4443 =
                let uu____4454 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____4454]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____4443;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4442  in
          let uu____4487 =
            (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
              env pure_c
             in
          match uu____4487 with
          | (m_c,g_lift) ->
              let uu____4498 =
                mk_bind env pure_c FStar_Pervasives_Native.None c flags r  in
              (match uu____4498 with
               | (bind_c,g_bind) ->
                   let uu____4509 =
                     FStar_TypeChecker_Env.conj_guard g_lift g_bind  in
                   (bind_c, uu____4509))
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____4522 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_4528  ->
              match uu___1_4528 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____4531 -> false))
       in
    if uu____4522
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_4543  ->
              match uu___2_4543 with
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
        let uu____4571 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4571
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____4582 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____4582  in
           let pure_assume_wp1 =
             let uu____4587 = FStar_TypeChecker_Env.get_range env  in
             let uu____4588 =
               let uu____4593 =
                 let uu____4594 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____4594]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____4593  in
             uu____4588 FStar_Pervasives_Native.None uu____4587  in
           let uu____4627 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           lift_wp_and_bind_with env pure_assume_wp1 c uu____4627)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____4655 =
          let uu____4656 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____4656 with
          | (c,g_c) ->
              let uu____4667 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____4667
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____4681 = weaken_comp env c f1  in
                     (match uu____4681 with
                      | (c1,g_w) ->
                          let uu____4692 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____4692)))
           in
        let uu____4693 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____4693 weaken
  
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
                 let uu____4750 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____4750  in
               let pure_assert_wp1 =
                 let uu____4755 =
                   let uu____4760 =
                     let uu____4761 =
                       let uu____4770 = label_opt env reason r f  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                         uu____4770
                        in
                     [uu____4761]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____4760
                    in
                 uu____4755 FStar_Pervasives_Native.None r  in
               lift_wp_and_bind_with env pure_assert_wp1 c flags)
  
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
            let uu____4840 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____4840
            then (lc, g0)
            else
              (let flags =
                 let uu____4852 =
                   let uu____4860 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____4860
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____4852 with
                 | (maybe_trivial_post,flags) ->
                     let uu____4890 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_4898  ->
                               match uu___3_4898 with
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
                               | uu____4901 -> []))
                        in
                     FStar_List.append flags uu____4890
                  in
               let strengthen uu____4911 =
                 let uu____4912 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____4912 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____4931 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____4931 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____4938 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____4938
                              then
                                let uu____4942 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____4944 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____4942 uu____4944
                              else ());
                             (let uu____4949 =
                                strengthen_comp env reason c f flags  in
                              match uu____4949 with
                              | (c1,g_s) ->
                                  let uu____4960 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____4960))))
                  in
               let uu____4961 =
                 let uu____4962 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____4962
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____4961,
                 (let uu___591_4964 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___591_4964.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___591_4964.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___591_4964.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_4973  ->
            match uu___4_4973 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____4977 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____5006 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____5006
          then e
          else
            (let uu____5013 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____5016 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____5016)
                in
             if uu____5013
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
          fun uu____5069  ->
            match uu____5069 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____5089 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____5089 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____5102 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____5102
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____5112 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____5112
                       then
                         let uu____5117 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____5117
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5124 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____5124
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5133 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____5133
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____5140 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____5140
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____5156 =
                  let uu____5157 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____5157
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____5165 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____5165, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____5168 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____5168 with
                     | (c1,g_c1) ->
                         let uu____5179 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____5179 with
                          | (c2,g_c2) ->
                              (debug1
                                 (fun uu____5199  ->
                                    let uu____5200 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____5202 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____5207 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____5200 uu____5202 uu____5207);
                               (let aux uu____5225 =
                                  let uu____5226 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____5226
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____5257
                                        ->
                                        let uu____5258 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____5258
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____5290 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____5290
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____5335 =
                                  let uu____5336 =
                                    let uu____5338 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____5338  in
                                  if uu____5336
                                  then
                                    let uu____5352 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____5352
                                     then
                                       FStar_Util.Inl
                                         (c2,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____5375 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____5375))
                                  else
                                    (let uu____5390 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____5390
                                     then
                                       let close1 x reason c =
                                         let x1 =
                                           let uu___661_5432 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___661_5432.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___661_5432.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           }  in
                                         let uu____5433 =
                                           let uu____5439 =
                                             close_comp_if_refinement_t env
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c
                                              in
                                           (uu____5439, reason)  in
                                         FStar_Util.Inl uu____5433  in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some
                                          e,FStar_Pervasives_Native.Some x)
                                           ->
                                           let uu____5475 =
                                             FStar_All.pipe_right c2
                                               (FStar_Syntax_Subst.subst_comp
                                                  [FStar_Syntax_Syntax.NT
                                                     (x, e)])
                                              in
                                           FStar_All.pipe_right uu____5475
                                             (close1 x "c1 Tot")
                                       | (uu____5489,FStar_Pervasives_Native.Some
                                          x) ->
                                           FStar_All.pipe_right c2
                                             (close1 x "c1 Tot only close")
                                       | (uu____5512,uu____5513) -> aux ()
                                     else
                                       (let uu____5528 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____5528
                                        then
                                          let uu____5541 =
                                            let uu____5547 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____5547, "both GTot")  in
                                          FStar_Util.Inl uu____5541
                                        else aux ()))
                                   in
                                let uu____5558 = try_simplify ()  in
                                match uu____5558 with
                                | FStar_Util.Inl (c,reason) ->
                                    (debug1
                                       (fun uu____5588  ->
                                          let uu____5589 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____5589);
                                     (let uu____5592 =
                                        FStar_TypeChecker_Env.conj_guard g_c1
                                          g_c2
                                         in
                                      (c, uu____5592)))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____5604  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 =
                                        let uu____5630 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____5630 with
                                        | (c,g_bind) ->
                                            let uu____5641 =
                                              let uu____5642 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g_c1 g_c2
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                uu____5642 g_bind
                                               in
                                            (c, uu____5641)
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
                                        let uu____5669 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____5669 with
                                        | (m,uu____5681,lift2) ->
                                            let uu____5683 =
                                              let uu____5688 =
                                                lift_comp env c22 lift2  in
                                              FStar_All.pipe_right uu____5688
                                                (fun uu____5705  ->
                                                   match uu____5705 with
                                                   | (c,g) ->
                                                       let uu____5716 =
                                                         FStar_Syntax_Syntax.mk_Comp
                                                           c
                                                          in
                                                       (uu____5716, g))
                                               in
                                            (match uu____5683 with
                                             | (c23,g2) ->
                                                 let uu____5723 =
                                                   destruct_comp c12  in
                                                 (match uu____5723 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let vc1 =
                                                        let uu____5741 =
                                                          let uu____5746 =
                                                            let uu____5747 =
                                                              FStar_All.pipe_right
                                                                md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                                                FStar_Util.must
                                                               in
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              uu____5747
                                                             in
                                                          let uu____5750 =
                                                            let uu____5751 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____5760 =
                                                              let uu____5771
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____5771]
                                                               in
                                                            uu____5751 ::
                                                              uu____5760
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____5746
                                                            uu____5750
                                                           in
                                                        uu____5741
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____5804 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____5804 with
                                                       | (c,g_s) ->
                                                           let uu____5819 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____5819))))
                                         in
                                      let c1_typ =
                                        FStar_TypeChecker_Env.unfold_effect_abbrev
                                          env c1
                                         in
                                      let uu____5821 =
                                        let uu____5828 =
                                          FStar_List.hd
                                            c1_typ.FStar_Syntax_Syntax.comp_univs
                                           in
                                        (uu____5828,
                                          (c1_typ.FStar_Syntax_Syntax.result_typ))
                                         in
                                      match uu____5821 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____5841 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____5841
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____5850 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____5850
                                             then
                                               (debug1
                                                  (fun uu____5864  ->
                                                     let uu____5865 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____5867 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____5865 uu____5867);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 mk_bind1 c1 b c21))
                                             else
                                               (let uu____5875 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____5878 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____5878)
                                                   in
                                                if uu____5875
                                                then
                                                  let e1' =
                                                    let uu____5903 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____5903
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug1
                                                     (fun uu____5915  ->
                                                        let uu____5916 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____5918 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____5916
                                                          uu____5918);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug1
                                                     (fun uu____5933  ->
                                                        let uu____5934 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____5936 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____5934
                                                          uu____5936);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____5943 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____5943
                                                       in
                                                    let uu____5944 =
                                                      let uu____5949 =
                                                        let uu____5950 =
                                                          let uu____5951 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____5951]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____5950
                                                         in
                                                      weaken_comp uu____5949
                                                        c21 x_eq_e
                                                       in
                                                    match uu____5944 with
                                                    | (c22,g_w) ->
                                                        let uu____5976 =
                                                          mk_bind1 c1 b c22
                                                           in
                                                        (match uu____5976
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____5987 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____5987))))))
                                          else mk_bind1 c1 b c2))))))
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
      | uu____6004 -> g2
  
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
            (let uu____6028 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____6028)
           in
        let flags =
          if should_return1
          then
            let uu____6036 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____6036
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____6054 =
          let uu____6055 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____6055 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____6068 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____6068
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____6076 =
                  let uu____6078 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____6078  in
                (if uu____6076
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___775_6087 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___775_6087.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___775_6087.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___775_6087.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____6088 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____6088, g_c)
                 else
                   (let uu____6091 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____6091, g_c)))
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
                   let uu____6102 =
                     let uu____6103 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____6103
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____6102
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____6106 =
                   let uu____6111 =
                     let uu____6112 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____6112
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____6111  in
                 match uu____6106 with
                 | (bind_c,g_bind) ->
                     let uu____6121 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____6122 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____6121, uu____6122))
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
            fun uu____6158  ->
              match uu____6158 with
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
                    let uu____6170 =
                      ((let uu____6174 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____6174) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____6170
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6192 =
        let uu____6193 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6193  in
      FStar_Syntax_Syntax.fvar uu____6192 FStar_Syntax_Syntax.delta_constant
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
               fun uu____6263  ->
                 match uu____6263 with
                 | (uu____6277,eff_label,uu____6279,uu____6280) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____6293 =
          let uu____6301 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____6339  ->
                    match uu____6339 with
                    | (uu____6354,uu____6355,flags,uu____6357) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_6374  ->
                                match uu___5_6374 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____6377 -> false))))
             in
          if uu____6301
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____6293 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____6414 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____6416 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____6416
              then
                let uu____6423 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                   in
                (uu____6423, FStar_TypeChecker_Env.trivial_guard)
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____6462 =
                     FStar_Syntax_Util.get_match_with_close_wps
                       md.FStar_Syntax_Syntax.match_wps
                      in
                   match uu____6462 with
                   | (if_then_else1,uu____6472,uu____6473) ->
                       let uu____6474 =
                         FStar_Range.union_ranges
                           wp_t.FStar_Syntax_Syntax.pos
                           wp_e.FStar_Syntax_Syntax.pos
                          in
                       let uu____6475 =
                         let uu____6480 =
                           FStar_TypeChecker_Env.inst_effect_fun_with
                             [u_res_t] env md if_then_else1
                            in
                         let uu____6481 =
                           let uu____6482 = FStar_Syntax_Syntax.as_arg res_t1
                              in
                           let uu____6491 =
                             let uu____6502 = FStar_Syntax_Syntax.as_arg g
                                in
                             let uu____6511 =
                               let uu____6522 =
                                 FStar_Syntax_Syntax.as_arg wp_t  in
                               let uu____6531 =
                                 let uu____6542 =
                                   FStar_Syntax_Syntax.as_arg wp_e  in
                                 [uu____6542]  in
                               uu____6522 :: uu____6531  in
                             uu____6502 :: uu____6511  in
                           uu____6482 :: uu____6491  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____6480 uu____6481
                          in
                       uu____6475 FStar_Pervasives_Native.None uu____6474
                    in
                 let default_case =
                   let post_k =
                     let uu____6595 =
                       let uu____6604 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____6604]  in
                     let uu____6623 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6595 uu____6623  in
                   let kwp =
                     let uu____6629 =
                       let uu____6638 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____6638]  in
                     let uu____6657 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6629 uu____6657  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____6664 =
                       let uu____6665 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____6665]  in
                     let uu____6684 =
                       let uu____6687 =
                         let uu____6694 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____6694
                          in
                       let uu____6695 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____6687 uu____6695  in
                     FStar_Syntax_Util.abs uu____6664 uu____6684
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
                   let uu____6719 =
                     should_not_inline_whole_match ||
                       (let uu____6722 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____6722)
                      in
                   if uu____6719 then cthen true else cthen false  in
                 let uu____6729 =
                   FStar_List.fold_right
                     (fun uu____6776  ->
                        fun uu____6777  ->
                          match (uu____6776, uu____6777) with
                          | ((g,eff_label,uu____6819,cthen),(celse,g_comp))
                              ->
                              let uu____6853 =
                                let uu____6858 = maybe_return eff_label cthen
                                   in
                                FStar_TypeChecker_Common.lcomp_comp
                                  uu____6858
                                 in
                              (match uu____6853 with
                               | (cthen1,gthen) ->
                                   let uu____6865 =
                                     lift_and_destruct env cthen1 celse  in
                                   (match uu____6865 with
                                    | ((md,uu____6897,uu____6898),(uu____6899,uu____6900,wp_then),
                                       (uu____6902,uu____6903,wp_else),g_lift)
                                        ->
                                        let uu____6924 =
                                          let uu____6925 =
                                            ifthenelse md res_t g wp_then
                                              wp_else
                                             in
                                          mk_comp md u_res_t res_t uu____6925
                                            []
                                           in
                                        let uu____6926 =
                                          let uu____6927 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_comp gthen
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            uu____6927 g_lift
                                           in
                                        (uu____6924, uu____6926)))) lcases
                     (default_case, FStar_TypeChecker_Env.trivial_guard)
                    in
                 match uu____6729 with
                 | (comp,g_comp) ->
                     (match lcases with
                      | [] -> (comp, g_comp)
                      | uu____6952::[] -> (comp, g_comp)
                      | uu____6995 ->
                          let comp1 =
                            FStar_TypeChecker_Env.comp_to_comp_typ env comp
                             in
                          let md =
                            FStar_TypeChecker_Env.get_effect_decl env
                              comp1.FStar_Syntax_Syntax.effect_name
                             in
                          let uu____7014 = destruct_comp comp1  in
                          (match uu____7014 with
                           | (uu____7025,uu____7026,wp) ->
                               let uu____7028 =
                                 FStar_Syntax_Util.get_match_with_close_wps
                                   md.FStar_Syntax_Syntax.match_wps
                                  in
                               (match uu____7028 with
                                | (uu____7039,ite_wp,uu____7041) ->
                                    let wp1 =
                                      let uu____7045 =
                                        let uu____7050 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [u_res_t] env md ite_wp
                                           in
                                        let uu____7051 =
                                          let uu____7052 =
                                            FStar_Syntax_Syntax.as_arg res_t
                                             in
                                          let uu____7061 =
                                            let uu____7072 =
                                              FStar_Syntax_Syntax.as_arg wp
                                               in
                                            [uu____7072]  in
                                          uu____7052 :: uu____7061  in
                                        FStar_Syntax_Syntax.mk_Tm_app
                                          uu____7050 uu____7051
                                         in
                                      uu____7045 FStar_Pervasives_Native.None
                                        wp.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____7105 =
                                      mk_comp md u_res_t res_t wp1
                                        bind_cases_flags
                                       in
                                    (uu____7105, g_comp)))))
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
          let uu____7139 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____7139 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____7155 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____7161 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____7155 uu____7161
              else
                (let uu____7170 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____7176 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____7170 uu____7176)
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
          let uu____7201 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____7201
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____7204 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____7204
        then u_res
        else
          (let is_total =
             let uu____7211 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____7211
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____7222 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____7222 with
              | FStar_Pervasives_Native.None  ->
                  let uu____7225 =
                    let uu____7231 =
                      let uu____7233 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____7233
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____7231)
                     in
                  FStar_Errors.raise_error uu____7225
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
      let uu____7257 = destruct_comp ct  in
      match uu____7257 with
      | (u_t,t,wp) ->
          let vc =
            let uu____7276 = FStar_TypeChecker_Env.get_range env  in
            let uu____7277 =
              let uu____7282 =
                let uu____7283 =
                  FStar_All.pipe_right md.FStar_Syntax_Syntax.trivial
                    FStar_Util.must
                   in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____7283
                 in
              let uu____7286 =
                let uu____7287 = FStar_Syntax_Syntax.as_arg t  in
                let uu____7296 =
                  let uu____7307 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____7307]  in
                uu____7287 :: uu____7296  in
              FStar_Syntax_Syntax.mk_Tm_app uu____7282 uu____7286  in
            uu____7277 FStar_Pervasives_Native.None uu____7276  in
          let uu____7340 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____7340)
  
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
               let uu____7381 =
                 let uu____7382 = FStar_Syntax_Subst.compress t2  in
                 uu____7382.FStar_Syntax_Syntax.n  in
               match uu____7381 with
               | FStar_Syntax_Syntax.Tm_type uu____7386 -> true
               | uu____7388 -> false  in
             let uu____7390 =
               let uu____7391 =
                 FStar_Syntax_Util.unrefine
                   lc.FStar_TypeChecker_Common.res_typ
                  in
               uu____7391.FStar_Syntax_Syntax.n  in
             match uu____7390 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____7399 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____7409 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____7409
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____7412 =
                     let uu____7413 =
                       let uu____7414 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____7414
                        in
                     (FStar_Pervasives_Native.None, uu____7413)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____7412
                    in
                 let e1 =
                   let uu____7420 =
                     let uu____7425 =
                       let uu____7426 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____7426]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____7425  in
                   uu____7420 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____7451 -> (e, lc))
  
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
          (let uu____7486 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____7486
           then
             let uu____7489 = FStar_Syntax_Print.term_to_string e  in
             let uu____7491 = FStar_TypeChecker_Common.lcomp_to_string lc  in
             let uu____7493 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____7489 uu____7491 uu____7493
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____7503 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____7503 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____7528 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____7554 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____7554, false)
             else
               (let uu____7564 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____7564, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____7577) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____7589 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____7589
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___959_7605 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___959_7605.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___959_7605.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___959_7605.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____7612 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____7612 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____7628 =
                      let uu____7629 = FStar_TypeChecker_Common.lcomp_comp lc
                         in
                      match uu____7629 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____7649 =
                            let uu____7651 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____7651 = FStar_Syntax_Util.Equal  in
                          if uu____7649
                          then
                            ((let uu____7658 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____7658
                              then
                                let uu____7662 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____7664 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____7662 uu____7664
                              else ());
                             (let uu____7669 = set_result_typ1 c  in
                              (uu____7669, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____7676 ->
                                   true
                               | uu____7684 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____7693 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____7693
                                  in
                               let lc1 =
                                 let uu____7695 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____7696 =
                                   let uu____7697 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____7697)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____7695 uu____7696
                                  in
                               ((let uu____7701 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____7701
                                 then
                                   let uu____7705 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____7707 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____7709 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____7711 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____7705 uu____7707 uu____7709
                                     uu____7711
                                 else ());
                                (let uu____7716 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____7716 with
                                 | (c1,g_lc) ->
                                     let uu____7727 = set_result_typ1 c1  in
                                     let uu____7728 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____7727, uu____7728)))
                             else
                               ((let uu____7732 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____7732
                                 then
                                   let uu____7736 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____7738 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____7736 uu____7738
                                 else ());
                                (let uu____7743 = set_result_typ1 c  in
                                 (uu____7743, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___996_7747 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___996_7747.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___996_7747.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___996_7747.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____7757 =
                      let uu____7758 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____7758
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____7768 =
                           let uu____7769 = FStar_Syntax_Subst.compress f1
                              in
                           uu____7769.FStar_Syntax_Syntax.n  in
                         match uu____7768 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____7776,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____7778;
                                           FStar_Syntax_Syntax.vars =
                                             uu____7779;_},uu____7780)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1012_7806 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1012_7806.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1012_7806.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1012_7806.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____7807 ->
                             let uu____7808 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____7808 with
                              | (c,g_c) ->
                                  ((let uu____7820 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____7820
                                    then
                                      let uu____7824 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____7826 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____7828 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____7830 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____7824 uu____7826 uu____7828
                                        uu____7830
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
                                        let uu____7843 =
                                          let uu____7848 =
                                            let uu____7849 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____7849]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____7848
                                           in
                                        uu____7843
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____7876 =
                                      let uu____7881 =
                                        FStar_All.pipe_left
                                          (fun _7902  ->
                                             FStar_Pervasives_Native.Some
                                               _7902)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____7903 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____7904 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____7905 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____7881
                                        uu____7903 e uu____7904 uu____7905
                                       in
                                    match uu____7876 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1030_7913 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1030_7913.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1030_7913.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____7915 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____7915
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____7918 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____7918 with
                                         | (c2,g_lc) ->
                                             ((let uu____7930 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____7930
                                               then
                                                 let uu____7934 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____7934
                                               else ());
                                              (let uu____7939 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____7939))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_7948  ->
                              match uu___6_7948 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____7951 -> []))
                       in
                    let lc1 =
                      let uu____7953 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____7953 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1046_7955 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1046_7955.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1046_7955.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1046_7955.FStar_TypeChecker_Common.implicits)
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
        let uu____7991 =
          let uu____7994 =
            let uu____7999 =
              let uu____8000 =
                let uu____8009 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____8009  in
              [uu____8000]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____7999  in
          uu____7994 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____7991  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____8032 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____8032
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____8051 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____8067 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____8084 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____8084
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____8100)::(ens,uu____8102)::uu____8103 ->
                    let uu____8146 =
                      let uu____8149 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____8149  in
                    let uu____8150 =
                      let uu____8151 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____8151  in
                    (uu____8146, uu____8150)
                | uu____8154 ->
                    let uu____8165 =
                      let uu____8171 =
                        let uu____8173 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____8173
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____8171)
                       in
                    FStar_Errors.raise_error uu____8165
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____8193)::uu____8194 ->
                    let uu____8221 =
                      let uu____8226 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____8226
                       in
                    (match uu____8221 with
                     | (us_r,uu____8258) ->
                         let uu____8259 =
                           let uu____8264 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____8264
                            in
                         (match uu____8259 with
                          | (us_e,uu____8296) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____8299 =
                                  let uu____8300 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8300
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8299
                                  us_r
                                 in
                              let as_ens =
                                let uu____8302 =
                                  let uu____8303 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8303
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8302
                                  us_e
                                 in
                              let req =
                                let uu____8307 =
                                  let uu____8312 =
                                    let uu____8313 =
                                      let uu____8324 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8324]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8313
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____8312
                                   in
                                uu____8307 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____8364 =
                                  let uu____8369 =
                                    let uu____8370 =
                                      let uu____8381 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8381]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8370
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____8369
                                   in
                                uu____8364 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____8418 =
                                let uu____8421 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____8421  in
                              let uu____8422 =
                                let uu____8423 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____8423  in
                              (uu____8418, uu____8422)))
                | uu____8426 -> failwith "Impossible"))
  
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
      (let uu____8460 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____8460
       then
         let uu____8465 = FStar_Syntax_Print.term_to_string tm  in
         let uu____8467 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____8465 uu____8467
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
        (let uu____8521 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____8521
         then
           let uu____8526 = FStar_Syntax_Print.term_to_string tm  in
           let uu____8528 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____8526
             uu____8528
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____8539 =
      let uu____8541 =
        let uu____8542 = FStar_Syntax_Subst.compress t  in
        uu____8542.FStar_Syntax_Syntax.n  in
      match uu____8541 with
      | FStar_Syntax_Syntax.Tm_app uu____8546 -> false
      | uu____8564 -> true  in
    if uu____8539
    then t
    else
      (let uu____8569 = FStar_Syntax_Util.head_and_args t  in
       match uu____8569 with
       | (head1,args) ->
           let uu____8612 =
             let uu____8614 =
               let uu____8615 = FStar_Syntax_Subst.compress head1  in
               uu____8615.FStar_Syntax_Syntax.n  in
             match uu____8614 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____8620 -> false  in
           if uu____8612
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____8652 ->
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
          ((let uu____8699 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____8699
            then
              let uu____8702 = FStar_Syntax_Print.term_to_string e  in
              let uu____8704 = FStar_Syntax_Print.term_to_string t  in
              let uu____8706 =
                let uu____8708 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____8708
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____8702 uu____8704 uu____8706
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____8721 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____8721 with
              | (formals,uu____8737) ->
                  let n_implicits =
                    let uu____8759 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____8837  ->
                              match uu____8837 with
                              | (uu____8845,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____8852 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____8852 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____8759 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____8977 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____8977 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____8991 =
                      let uu____8997 =
                        let uu____8999 = FStar_Util.string_of_int n_expected
                           in
                        let uu____9001 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____9003 = FStar_Util.string_of_int n_available
                           in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____8999 uu____9001 uu____9003
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____8997)
                       in
                    let uu____9007 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____8991 uu____9007
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_9025 =
              match uu___7_9025 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____9068 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____9068 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _9199,uu____9186) when
                           _9199 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____9232,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Implicit
                                      uu____9234))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____9268 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____9268 with
                            | (v1,uu____9309,g) ->
                                ((let uu____9324 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____9324
                                  then
                                    let uu____9327 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____9327
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____9337 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____9337 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____9430 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____9430))))
                       | (uu____9457,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____9494 =
                             let uu____9507 =
                               let uu____9514 =
                                 let uu____9519 = FStar_Dyn.mkdyn env  in
                                 (uu____9519, tau)  in
                               FStar_Pervasives_Native.Some uu____9514  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____9507
                              in
                           (match uu____9494 with
                            | (v1,uu____9552,g) ->
                                ((let uu____9567 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____9567
                                  then
                                    let uu____9570 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____9570
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____9580 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____9580 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____9673 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____9673))))
                       | (uu____9700,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____9748 =
                       let uu____9775 = inst_n_binders t1  in
                       aux [] uu____9775 bs1  in
                     (match uu____9748 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____9847) -> (e, torig, guard)
                           | (uu____9878,[]) when
                               let uu____9909 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____9909 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____9911 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____9939 ->
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
            | uu____9952 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____9964 =
      let uu____9968 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____9968
        (FStar_List.map
           (fun u  ->
              let uu____9980 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____9980 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____9964 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____10008 = FStar_Util.set_is_empty x  in
      if uu____10008
      then []
      else
        (let s =
           let uu____10026 =
             let uu____10029 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____10029  in
           FStar_All.pipe_right uu____10026 FStar_Util.set_elements  in
         (let uu____10045 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____10045
          then
            let uu____10050 =
              let uu____10052 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____10052  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____10050
          else ());
         (let r =
            let uu____10061 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____10061  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____10100 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____10100
                     then
                       let uu____10105 =
                         let uu____10107 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____10107
                          in
                       let uu____10111 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____10113 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____10105 uu____10111 uu____10113
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
        let uu____10143 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____10143 FStar_Util.set_elements  in
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
        | ([],uu____10182) -> generalized_univ_names
        | (uu____10189,[]) -> explicit_univ_names
        | uu____10196 ->
            let uu____10205 =
              let uu____10211 =
                let uu____10213 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____10213
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____10211)
               in
            FStar_Errors.raise_error uu____10205 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____10235 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____10235
       then
         let uu____10240 = FStar_Syntax_Print.term_to_string t  in
         let uu____10242 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____10240 uu____10242
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____10251 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____10251
        then
          let uu____10256 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____10256
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____10265 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____10265
         then
           let uu____10270 = FStar_Syntax_Print.term_to_string t  in
           let uu____10272 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____10270 uu____10272
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
        let uu____10356 =
          let uu____10358 =
            FStar_Util.for_all
              (fun uu____10372  ->
                 match uu____10372 with
                 | (uu____10382,uu____10383,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____10358  in
        if uu____10356
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____10435 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____10435
              then
                let uu____10438 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____10438
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____10445 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____10445
               then
                 let uu____10448 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____10448
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____10466 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____10466 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____10500 =
             match uu____10500 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____10537 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____10537
                   then
                     let uu____10542 =
                       let uu____10544 =
                         let uu____10548 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____10548
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____10544
                         (FStar_String.concat ", ")
                        in
                     let uu____10596 =
                       let uu____10598 =
                         let uu____10602 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____10602
                           (FStar_List.map
                              (fun u  ->
                                 let uu____10615 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____10617 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____10615
                                   uu____10617))
                          in
                       FStar_All.pipe_right uu____10598
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____10542
                       uu____10596
                   else ());
                  (let univs2 =
                     let uu____10631 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____10643 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____10643) univs1
                       uu____10631
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____10650 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____10650
                    then
                      let uu____10655 =
                        let uu____10657 =
                          let uu____10661 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____10661
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____10657
                          (FStar_String.concat ", ")
                         in
                      let uu____10709 =
                        let uu____10711 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____10725 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____10727 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____10725
                                    uu____10727))
                           in
                        FStar_All.pipe_right uu____10711
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____10655 uu____10709
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____10748 =
             let uu____10765 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____10765  in
           match uu____10748 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____10855 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____10855
                 then ()
                 else
                   (let uu____10860 = lec_hd  in
                    match uu____10860 with
                    | (lb1,uu____10868,uu____10869) ->
                        let uu____10870 = lec2  in
                        (match uu____10870 with
                         | (lb2,uu____10878,uu____10879) ->
                             let msg =
                               let uu____10882 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10884 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____10882 uu____10884
                                in
                             let uu____10887 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____10887))
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
                 let uu____10955 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____10955
                 then ()
                 else
                   (let uu____10960 = lec_hd  in
                    match uu____10960 with
                    | (lb1,uu____10968,uu____10969) ->
                        let uu____10970 = lec2  in
                        (match uu____10970 with
                         | (lb2,uu____10978,uu____10979) ->
                             let msg =
                               let uu____10982 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10984 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____10982 uu____10984
                                in
                             let uu____10987 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____10987))
                  in
               let lecs1 =
                 let uu____10998 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____11051 = univs_and_uvars_of_lec this_lec  in
                        match uu____11051 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____10998 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____11156 = lec_hd  in
                   match uu____11156 with
                   | (lbname,e,c) ->
                       let uu____11166 =
                         let uu____11172 =
                           let uu____11174 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____11176 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____11178 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____11174 uu____11176 uu____11178
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____11172)
                          in
                       let uu____11182 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____11166 uu____11182
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____11201 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____11201 with
                         | FStar_Pervasives_Native.Some uu____11210 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____11218 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____11222 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____11222 with
                              | (bs,kres) ->
                                  ((let uu____11266 =
                                      let uu____11267 =
                                        let uu____11270 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____11270
                                         in
                                      uu____11267.FStar_Syntax_Syntax.n  in
                                    match uu____11266 with
                                    | FStar_Syntax_Syntax.Tm_type uu____11271
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____11275 =
                                          let uu____11277 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____11277  in
                                        if uu____11275
                                        then fail1 kres
                                        else ()
                                    | uu____11282 -> fail1 kres);
                                   (let a =
                                      let uu____11284 =
                                        let uu____11287 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _11290  ->
                                             FStar_Pervasives_Native.Some
                                               _11290) uu____11287
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____11284
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____11298 ->
                                          let uu____11307 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____11307
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
                      (fun uu____11410  ->
                         match uu____11410 with
                         | (lbname,e,c) ->
                             let uu____11456 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____11517 ->
                                   let uu____11530 = (e, c)  in
                                   (match uu____11530 with
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
                                                (fun uu____11570  ->
                                                   match uu____11570 with
                                                   | (x,uu____11576) ->
                                                       let uu____11577 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____11577)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____11595 =
                                                let uu____11597 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____11597
                                                 in
                                              if uu____11595
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
                                          let uu____11606 =
                                            let uu____11607 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____11607.FStar_Syntax_Syntax.n
                                             in
                                          match uu____11606 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____11632 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____11632 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____11643 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____11647 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____11647, gen_tvars))
                                in
                             (match uu____11456 with
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
        (let uu____11794 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____11794
         then
           let uu____11797 =
             let uu____11799 =
               FStar_List.map
                 (fun uu____11814  ->
                    match uu____11814 with
                    | (lb,uu____11823,uu____11824) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____11799 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____11797
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____11850  ->
                match uu____11850 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____11879 = gen env is_rec lecs  in
           match uu____11879 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____11978  ->
                       match uu____11978 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____12040 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____12040
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____12088  ->
                           match uu____12088 with
                           | (l,us,e,c,gvs) ->
                               let uu____12122 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____12124 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____12126 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____12128 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____12130 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____12122 uu____12124 uu____12126
                                 uu____12128 uu____12130))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____12175  ->
                match uu____12175 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____12219 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____12219, t, c, gvs)) univnames_lecs
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
              (let uu____12280 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____12280 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____12286 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _12289  -> FStar_Pervasives_Native.Some _12289)
                     uu____12286)
             in
          let is_var e1 =
            let uu____12297 =
              let uu____12298 = FStar_Syntax_Subst.compress e1  in
              uu____12298.FStar_Syntax_Syntax.n  in
            match uu____12297 with
            | FStar_Syntax_Syntax.Tm_name uu____12302 -> true
            | uu____12304 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1502_12325 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1502_12325.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1502_12325.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____12326 -> e2  in
          let env2 =
            let uu___1505_12328 = env1  in
            let uu____12329 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1505_12328.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1505_12328.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1505_12328.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1505_12328.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1505_12328.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1505_12328.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1505_12328.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1505_12328.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1505_12328.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1505_12328.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1505_12328.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1505_12328.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1505_12328.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1505_12328.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1505_12328.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1505_12328.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1505_12328.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____12329;
              FStar_TypeChecker_Env.is_iface =
                (uu___1505_12328.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1505_12328.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1505_12328.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1505_12328.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1505_12328.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1505_12328.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1505_12328.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1505_12328.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1505_12328.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1505_12328.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1505_12328.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1505_12328.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1505_12328.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1505_12328.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1505_12328.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1505_12328.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1505_12328.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1505_12328.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1505_12328.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1505_12328.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1505_12328.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1505_12328.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1505_12328.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1505_12328.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1505_12328.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1505_12328.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1505_12328.FStar_TypeChecker_Env.strict_args_tab)
            }  in
          let uu____12331 = check1 env2 t1 t2  in
          match uu____12331 with
          | FStar_Pervasives_Native.None  ->
              let uu____12338 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____12344 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____12338 uu____12344
          | FStar_Pervasives_Native.Some g ->
              ((let uu____12351 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12351
                then
                  let uu____12356 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____12356
                else ());
               (let uu____12362 = decorate e t2  in (uu____12362, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____12390 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____12390
         then
           let uu____12393 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____12393
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____12407 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____12407 with
         | (c,g_c) ->
             let uu____12419 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____12419
             then
               let uu____12427 =
                 let uu____12429 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____12429  in
               (uu____12427, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____12437 =
                    let uu____12438 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____12438
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____12437
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____12439 = check_trivial_precondition env c1  in
                match uu____12439 with
                | (ct,vc,g_pre) ->
                    ((let uu____12455 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____12455
                      then
                        let uu____12460 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____12460
                      else ());
                     (let uu____12465 =
                        let uu____12467 =
                          let uu____12468 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____12468  in
                        discharge uu____12467  in
                      let uu____12469 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____12465, uu____12469)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_12503 =
        match uu___8_12503 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____12513)::[] -> f fst1
        | uu____12538 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____12550 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____12550
          (fun _12551  -> FStar_TypeChecker_Common.NonTrivial _12551)
         in
      let op_or_e e =
        let uu____12562 =
          let uu____12563 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____12563  in
        FStar_All.pipe_right uu____12562
          (fun _12566  -> FStar_TypeChecker_Common.NonTrivial _12566)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _12573  -> FStar_TypeChecker_Common.NonTrivial _12573)
         in
      let op_or_t t =
        let uu____12584 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____12584
          (fun _12587  -> FStar_TypeChecker_Common.NonTrivial _12587)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _12594  -> FStar_TypeChecker_Common.NonTrivial _12594)
         in
      let short_op_ite uu___9_12600 =
        match uu___9_12600 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____12610)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____12637)::[] ->
            let uu____12678 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____12678
              (fun _12679  -> FStar_TypeChecker_Common.NonTrivial _12679)
        | uu____12680 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____12692 =
          let uu____12700 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____12700)  in
        let uu____12708 =
          let uu____12718 =
            let uu____12726 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____12726)  in
          let uu____12734 =
            let uu____12744 =
              let uu____12752 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____12752)  in
            let uu____12760 =
              let uu____12770 =
                let uu____12778 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____12778)  in
              let uu____12786 =
                let uu____12796 =
                  let uu____12804 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____12804)  in
                [uu____12796; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____12770 :: uu____12786  in
            uu____12744 :: uu____12760  in
          uu____12718 :: uu____12734  in
        uu____12692 :: uu____12708  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____12866 =
            FStar_Util.find_map table
              (fun uu____12881  ->
                 match uu____12881 with
                 | (x,mk1) ->
                     let uu____12898 = FStar_Ident.lid_equals x lid  in
                     if uu____12898
                     then
                       let uu____12903 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____12903
                     else FStar_Pervasives_Native.None)
             in
          (match uu____12866 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____12907 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____12915 =
      let uu____12916 = FStar_Syntax_Util.un_uinst l  in
      uu____12916.FStar_Syntax_Syntax.n  in
    match uu____12915 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____12921 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____12957)::uu____12958 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____12977 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____12986,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____12987))::uu____12988 -> bs
      | uu____13006 ->
          let uu____13007 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____13007 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____13011 =
                 let uu____13012 = FStar_Syntax_Subst.compress t  in
                 uu____13012.FStar_Syntax_Syntax.n  in
               (match uu____13011 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____13016) ->
                    let uu____13037 =
                      FStar_Util.prefix_until
                        (fun uu___10_13077  ->
                           match uu___10_13077 with
                           | (uu____13085,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____13086)) ->
                               false
                           | uu____13091 -> true) bs'
                       in
                    (match uu____13037 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____13127,uu____13128) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____13200,uu____13201) ->
                         let uu____13274 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____13294  ->
                                   match uu____13294 with
                                   | (x,uu____13303) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____13274
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____13352  ->
                                     match uu____13352 with
                                     | (x,i) ->
                                         let uu____13371 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____13371, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____13382 -> bs))
  
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
            let uu____13411 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____13411
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
          let uu____13442 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____13442
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
        (let uu____13485 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____13485
         then
           ((let uu____13490 = FStar_Ident.text_of_lid lident  in
             d uu____13490);
            (let uu____13492 = FStar_Ident.text_of_lid lident  in
             let uu____13494 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____13492 uu____13494))
         else ());
        (let fv =
           let uu____13500 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____13500
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
         let uu____13512 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1662_13514 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1662_13514.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1662_13514.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1662_13514.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1662_13514.FStar_Syntax_Syntax.sigattrs)
           }), uu____13512))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_13532 =
        match uu___11_13532 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____13535 -> false  in
      let reducibility uu___12_13543 =
        match uu___12_13543 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____13550 -> false  in
      let assumption uu___13_13558 =
        match uu___13_13558 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____13562 -> false  in
      let reification uu___14_13570 =
        match uu___14_13570 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____13573 -> true
        | uu____13575 -> false  in
      let inferred uu___15_13583 =
        match uu___15_13583 with
        | FStar_Syntax_Syntax.Discriminator uu____13585 -> true
        | FStar_Syntax_Syntax.Projector uu____13587 -> true
        | FStar_Syntax_Syntax.RecordType uu____13593 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____13603 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____13616 -> false  in
      let has_eq uu___16_13624 =
        match uu___16_13624 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____13628 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____13707 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____13714 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____13725 =
        let uu____13727 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___17_13733  ->
                  match uu___17_13733 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____13736 -> false))
           in
        FStar_All.pipe_right uu____13727 Prims.op_Negation  in
      if uu____13725
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____13757 =
            let uu____13763 =
              let uu____13765 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____13765 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____13763)  in
          FStar_Errors.raise_error uu____13757 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____13783 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____13791 =
            let uu____13793 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____13793  in
          if uu____13791 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____13803),uu____13804) ->
              ((let uu____13816 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____13816
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____13825 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____13825
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____13836 ->
              let uu____13845 =
                let uu____13847 =
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
                Prims.op_Negation uu____13847  in
              if uu____13845 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____13857 ->
              let uu____13864 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____13864 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____13872 ->
              let uu____13879 =
                let uu____13881 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____13881  in
              if uu____13879 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____13891 ->
              let uu____13892 =
                let uu____13894 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____13894  in
              if uu____13892 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13904 ->
              let uu____13905 =
                let uu____13907 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____13907  in
              if uu____13905 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13917 ->
              let uu____13930 =
                let uu____13932 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____13932  in
              if uu____13930 then err'1 () else ()
          | uu____13942 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let has_erased_for_extraction_attr fv =
        let uu____13965 =
          let uu____13970 =
            FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
          FStar_All.pipe_right uu____13970
            (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
           in
        FStar_All.pipe_right uu____13965
          (fun l_opt  ->
             (FStar_Util.is_some l_opt) &&
               (let uu____13989 = FStar_All.pipe_right l_opt FStar_Util.must
                   in
                FStar_All.pipe_right uu____13989
                  (FStar_List.existsb
                     (fun t1  ->
                        let uu____14007 =
                          let uu____14008 = FStar_Syntax_Subst.compress t1
                             in
                          uu____14008.FStar_Syntax_Syntax.n  in
                        match uu____14007 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            FStar_Ident.lid_equals
                              (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              FStar_Parser_Const.must_erase_for_extraction_attr
                            -> true
                        | uu____14014 -> false))))
         in
      let rec aux_whnf env t1 =
        let uu____14040 =
          let uu____14041 = FStar_Syntax_Subst.compress t1  in
          uu____14041.FStar_Syntax_Syntax.n  in
        match uu____14040 with
        | FStar_Syntax_Syntax.Tm_type uu____14045 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (has_erased_for_extraction_attr fv)
        | FStar_Syntax_Syntax.Tm_arrow uu____14048 ->
            let uu____14063 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____14063 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____14096 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____14096
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____14102;
               FStar_Syntax_Syntax.index = uu____14103;
               FStar_Syntax_Syntax.sort = t2;_},uu____14105)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14114,uu____14115) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____14157::[]) ->
            let uu____14196 =
              let uu____14197 = FStar_Syntax_Util.un_uinst head1  in
              uu____14197.FStar_Syntax_Syntax.n  in
            (match uu____14196 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.erased_lid)
                   || (has_erased_for_extraction_attr fv)
             | uu____14202 -> false)
        | uu____14204 -> false
      
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
        (let uu____14214 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____14214
         then
           let uu____14219 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____14219
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
              let uu____14266 =
                let uu____14267 = FStar_Syntax_Subst.compress signature  in
                uu____14267.FStar_Syntax_Syntax.n  in
              match uu____14266 with
              | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14271) when
                  (FStar_List.length bs) = (Prims.of_int (2)) ->
                  let uu____14300 = FStar_Syntax_Subst.open_binders bs  in
                  (match uu____14300 with
                   | (a,uu____14302)::(wp,uu____14304)::[] ->
                       FStar_All.pipe_right wp.FStar_Syntax_Syntax.sort
                         (FStar_Syntax_Subst.subst
                            [FStar_Syntax_Syntax.NT (a, a_tm)]))
              | uu____14333 ->
                  let uu____14334 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name signature
                     in
                  FStar_Errors.raise_error uu____14334 r
               in
            let uu____14340 =
              let uu____14353 =
                let uu____14355 = FStar_Range.string_of_range r  in
                FStar_Util.format2 "implicit for wp of %s at %s"
                  eff_name.FStar_Ident.str uu____14355
                 in
              new_implicit_var uu____14353 r env wp_sort  in
            match uu____14340 with
            | (wp_uvar,uu____14363,g_wp_uvar) ->
                let eff_c =
                  let uu____14378 =
                    let uu____14379 =
                      let uu____14390 =
                        FStar_All.pipe_right wp_uvar
                          FStar_Syntax_Syntax.as_arg
                         in
                      [uu____14390]  in
                    {
                      FStar_Syntax_Syntax.comp_univs = [u];
                      FStar_Syntax_Syntax.effect_name = eff_name;
                      FStar_Syntax_Syntax.result_typ = a_tm;
                      FStar_Syntax_Syntax.effect_args = uu____14379;
                      FStar_Syntax_Syntax.flags = []
                    }  in
                  FStar_Syntax_Syntax.mk_Comp uu____14378  in
                let uu____14423 =
                  let uu____14424 =
                    let uu____14431 =
                      let uu____14432 =
                        let uu____14447 =
                          let uu____14456 =
                            FStar_Syntax_Syntax.null_binder
                              FStar_Syntax_Syntax.t_unit
                             in
                          [uu____14456]  in
                        (uu____14447, eff_c)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____14432  in
                    FStar_Syntax_Syntax.mk uu____14431  in
                  uu____14424 FStar_Pervasives_Native.None r  in
                (uu____14423, g_wp_uvar)
  
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
                  let uu____14535 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____14535 r  in
                let uu____14545 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____14545 with
                | (uu____14554,signature) ->
                    let uu____14556 =
                      let uu____14557 = FStar_Syntax_Subst.compress signature
                         in
                      uu____14557.FStar_Syntax_Syntax.n  in
                    (match uu____14556 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14565) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____14613 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____14628 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____14630 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____14628 eff_name.FStar_Ident.str
                                       uu____14630) r
                                 in
                              (match uu____14613 with
                               | (is,g) ->
                                   let repr =
                                     let uu____14644 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts [u]
                                        in
                                     FStar_All.pipe_right uu____14644
                                       FStar_Pervasives_Native.snd
                                      in
                                   let uu____14653 =
                                     let uu____14654 =
                                       let uu____14659 =
                                         FStar_List.map
                                           FStar_Syntax_Syntax.as_arg (a_tm
                                           :: is)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr
                                         uu____14659
                                        in
                                     uu____14654 FStar_Pervasives_Native.None
                                       r
                                      in
                                   (uu____14653, g))
                          | uu____14668 -> fail1 signature)
                     | uu____14669 -> fail1 signature)
  
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
            let uu____14700 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____14700
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
              let uu____14745 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____14745 with
              | (uu____14750,sig_tm) ->
                  let fail1 t =
                    let uu____14758 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____14758 r  in
                  let uu____14764 =
                    let uu____14765 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____14765.FStar_Syntax_Syntax.n  in
                  (match uu____14764 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14769) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____14792)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____14814 -> fail1 sig_tm)
                   | uu____14815 -> fail1 sig_tm)
  
let (lift_tf_layered_effect :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.tscheme -> FStar_TypeChecker_Env.lift_comp_t)
  =
  fun tgt  ->
    fun lift_ts  ->
      fun env  ->
        fun c  ->
          (let uu____14836 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____14836
           then
             let uu____14841 = FStar_Syntax_Print.comp_to_string c  in
             let uu____14843 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____14841 uu____14843
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let effect_args_from_repr repr is_layered =
             let err uu____14873 =
               let uu____14874 =
                 let uu____14880 =
                   let uu____14882 = FStar_Syntax_Print.term_to_string repr
                      in
                   let uu____14884 = FStar_Util.string_of_bool is_layered  in
                   FStar_Util.format2
                     "Could not get effect args from repr %s with is_layered %s"
                     uu____14882 uu____14884
                    in
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____14880)  in
               FStar_Errors.raise_error uu____14874 r  in
             let repr1 = FStar_Syntax_Subst.compress repr  in
             if is_layered
             then
               match repr1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_app (uu____14896,uu____14897::is) ->
                   FStar_All.pipe_right is
                     (FStar_List.map FStar_Pervasives_Native.fst)
               | uu____14965 -> err ()
             else
               (match repr1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (uu____14970,c1) ->
                    let uu____14992 =
                      FStar_All.pipe_right c1
                        FStar_Syntax_Util.comp_to_comp_typ
                       in
                    FStar_All.pipe_right uu____14992
                      (fun ct  ->
                         FStar_All.pipe_right
                           ct.FStar_Syntax_Syntax.effect_args
                           (FStar_List.map FStar_Pervasives_Native.fst))
                | uu____15027 -> err ())
              in
           let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____15029 =
             let uu____15040 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____15041 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____15040, (ct.FStar_Syntax_Syntax.result_typ), uu____15041)
              in
           match uu____15029 with
           | (u,a,c_is) ->
               let uu____15089 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____15089 with
                | (uu____15098,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____15109 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____15111 = FStar_Ident.string_of_lid tgt  in
                      let uu____15113 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____15109 uu____15111 s uu____15113
                       in
                    let uu____15116 =
                      let uu____15149 =
                        let uu____15150 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____15150.FStar_Syntax_Syntax.n  in
                      match uu____15149 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____15214 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____15214 with
                           | (a_b::bs1,c2) ->
                               let uu____15274 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               let uu____15336 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____15274, uu____15336))
                      | uu____15363 ->
                          let uu____15364 =
                            let uu____15370 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____15370)
                             in
                          FStar_Errors.raise_error uu____15364 r
                       in
                    (match uu____15116 with
                     | (a_b,(rest_bs,f_b::[]),lift_ct) ->
                         let uu____15488 =
                           let uu____15495 =
                             let uu____15496 =
                               let uu____15497 =
                                 let uu____15504 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____15504, a)  in
                               FStar_Syntax_Syntax.NT uu____15497  in
                             [uu____15496]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____15495
                             (fun b  ->
                                let uu____15521 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____15523 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____15525 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____15527 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____15521 uu____15523 uu____15525
                                  uu____15527) r
                            in
                         (match uu____15488 with
                          | (rest_bs_uvars,g) ->
                              let substs =
                                FStar_List.map2
                                  (fun b  ->
                                     fun t  ->
                                       let uu____15564 =
                                         let uu____15571 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____15571, t)  in
                                       FStar_Syntax_Syntax.NT uu____15564)
                                  (a_b :: rest_bs) (a :: rest_bs_uvars)
                                 in
                              let guard_f =
                                let f_sort =
                                  let uu____15590 =
                                    FStar_All.pipe_right
                                      (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                      (FStar_Syntax_Subst.subst substs)
                                     in
                                  FStar_All.pipe_right uu____15590
                                    FStar_Syntax_Subst.compress
                                   in
                                let f_sort_is =
                                  let uu____15596 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env ct.FStar_Syntax_Syntax.effect_name
                                     in
                                  effect_args_from_repr f_sort uu____15596
                                   in
                                FStar_List.fold_left2
                                  (fun g1  ->
                                     fun i1  ->
                                       fun i2  ->
                                         let uu____15605 =
                                           FStar_TypeChecker_Rel.teq env i1
                                             i2
                                            in
                                         FStar_TypeChecker_Env.conj_guard g1
                                           uu____15605)
                                  FStar_TypeChecker_Env.trivial_guard c_is
                                  f_sort_is
                                 in
                              let is =
                                let uu____15609 =
                                  FStar_TypeChecker_Env.is_layered_effect env
                                    tgt
                                   in
                                effect_args_from_repr
                                  lift_ct.FStar_Syntax_Syntax.result_typ
                                  uu____15609
                                 in
                              let c1 =
                                let uu____15612 =
                                  let uu____15613 =
                                    let uu____15624 =
                                      FStar_All.pipe_right is
                                        (FStar_List.map
                                           (FStar_Syntax_Subst.subst substs))
                                       in
                                    FStar_All.pipe_right uu____15624
                                      (FStar_List.map
                                         FStar_Syntax_Syntax.as_arg)
                                     in
                                  {
                                    FStar_Syntax_Syntax.comp_univs =
                                      (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                    FStar_Syntax_Syntax.effect_name = tgt;
                                    FStar_Syntax_Syntax.result_typ = a;
                                    FStar_Syntax_Syntax.effect_args =
                                      uu____15613;
                                    FStar_Syntax_Syntax.flags =
                                      (ct.FStar_Syntax_Syntax.flags)
                                  }  in
                                FStar_Syntax_Syntax.mk_Comp uu____15612  in
                              ((let uu____15644 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____15644
                                then
                                  let uu____15649 =
                                    FStar_Syntax_Print.comp_to_string c1  in
                                  FStar_Util.print1 "} Lifted comp: %s\n"
                                    uu____15649
                                else ());
                               (let uu____15654 =
                                  FStar_TypeChecker_Env.conj_guard g guard_f
                                   in
                                (c1, uu____15654)))))))
  