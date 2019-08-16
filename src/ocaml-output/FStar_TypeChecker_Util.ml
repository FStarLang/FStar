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
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____1067 = destruct_comp c  in
        match uu____1067 with
        | (u,uu____1075,wp) ->
            let uu____1077 =
              let uu____1088 =
                let uu____1097 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____1097  in
              [uu____1088]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____1077;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____1130 =
          let uu____1137 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____1138 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____1137 uu____1138  in
        match uu____1130 with | (m,uu____1140,uu____1141) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____1158 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2)
           in
        if uu____1158
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
        let uu____1205 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____1205 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____1242 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____1242 with
             | (a,kwp) ->
                 let uu____1273 = destruct_comp m1  in
                 let uu____1280 = destruct_comp m2  in
                 ((md, a, kwp), uu____1273, uu____1280))
  
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
            let uu____1365 =
              let uu____1366 =
                let uu____1377 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____1377]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____1366;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____1365
  
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
          let uu____1461 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____1461
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1473 =
      let uu____1474 = FStar_Syntax_Subst.compress t  in
      uu____1474.FStar_Syntax_Syntax.n  in
    match uu____1473 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1478 -> true
    | uu____1494 -> false
  
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
              let uu____1564 =
                let uu____1566 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____1566  in
              if uu____1564
              then f
              else (let uu____1573 = reason1 ()  in label uu____1573 r f)
  
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
            let uu___234_1594 = g  in
            let uu____1595 =
              let uu____1596 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____1596  in
            {
              FStar_TypeChecker_Common.guard_f = uu____1595;
              FStar_TypeChecker_Common.deferred =
                (uu___234_1594.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___234_1594.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___234_1594.FStar_TypeChecker_Common.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____1617 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____1617
        then c
        else
          (let uu____1622 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____1622
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let uu____1663 =
                  FStar_Syntax_Util.get_match_with_close_wps
                    md.FStar_Syntax_Syntax.match_wps
                   in
                match uu____1663 with
                | (uu____1672,uu____1673,close1) ->
                    FStar_List.fold_right
                      (fun x  ->
                         fun wp  ->
                           let bs =
                             let uu____1696 = FStar_Syntax_Syntax.mk_binder x
                                in
                             [uu____1696]  in
                           let us =
                             let uu____1718 =
                               let uu____1721 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               [uu____1721]  in
                             u_res :: uu____1718  in
                           let wp1 =
                             FStar_Syntax_Util.abs bs wp
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None
                                     [FStar_Syntax_Syntax.TOTAL]))
                              in
                           let uu____1727 =
                             let uu____1732 =
                               FStar_TypeChecker_Env.inst_effect_fun_with us
                                 env md close1
                                in
                             let uu____1733 =
                               let uu____1734 =
                                 FStar_Syntax_Syntax.as_arg res_t  in
                               let uu____1743 =
                                 let uu____1754 =
                                   FStar_Syntax_Syntax.as_arg
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let uu____1763 =
                                   let uu____1774 =
                                     FStar_Syntax_Syntax.as_arg wp1  in
                                   [uu____1774]  in
                                 uu____1754 :: uu____1763  in
                               uu____1734 :: uu____1743  in
                             FStar_Syntax_Syntax.mk_Tm_app uu____1732
                               uu____1733
                              in
                           uu____1727 FStar_Pervasives_Native.None
                             wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____1816 = destruct_comp c1  in
              match uu____1816 with
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
                let uu____1856 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____1856
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
              ({ FStar_Syntax_Syntax.ppname = uu____1879;
                 FStar_Syntax_Syntax.index = uu____1880;
                 FStar_Syntax_Syntax.sort =
                   { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____1882;
                     FStar_Syntax_Syntax.vars = uu____1883;_};_},uu____1884)
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
              close_comp env [x] c
          | uu____1892 -> c
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_1904  ->
            match uu___0_1904 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____1907 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____1932 =
            let uu____1935 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____1935 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____1932
            (fun c  ->
               (let uu____1991 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____1991) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____1995 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____1995)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____2006 = FStar_Syntax_Util.head_and_args' e  in
                match uu____2006 with
                | (head1,uu____2023) ->
                    let uu____2044 =
                      let uu____2045 = FStar_Syntax_Util.un_uinst head1  in
                      uu____2045.FStar_Syntax_Syntax.n  in
                    (match uu____2044 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2050 =
                           let uu____2052 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____2052
                            in
                         Prims.op_Negation uu____2050
                     | uu____2053 -> true)))
              &&
              (let uu____2056 = should_not_inline_lc lc  in
               Prims.op_Negation uu____2056)
  
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
            let uu____2084 =
              let uu____2086 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____2086  in
            if uu____2084
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____2093 = FStar_Syntax_Util.is_unit t  in
               if uu____2093
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
                    let uu____2102 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____2102
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____2107 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____2107 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____2117 =
                             let uu____2118 =
                               let uu____2123 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____2124 =
                                 let uu____2125 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____2134 =
                                   let uu____2145 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____2145]  in
                                 uu____2125 :: uu____2134  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____2123
                                 uu____2124
                                in
                             uu____2118 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____2117)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____2179 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____2179
           then
             let uu____2184 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____2186 = FStar_Syntax_Print.term_to_string v1  in
             let uu____2188 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____2184 uu____2186 uu____2188
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
                let uu____2226 =
                  FStar_TypeChecker_Env.monad_leq env
                    FStar_Parser_Const.effect_PURE_lid
                    md.FStar_Syntax_Syntax.mname
                   in
                match uu____2226 with
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
              let uu____2232 =
                let uu____2237 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [FStar_Syntax_Syntax.U_zero; u_res_t] env md
                    md.FStar_Syntax_Syntax.bind_wp
                   in
                let uu____2238 =
                  let uu____2239 =
                    let uu____2248 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_range r))
                        FStar_Pervasives_Native.None r
                       in
                    FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____2248
                     in
                  let uu____2257 =
                    let uu____2268 =
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        FStar_Syntax_Syntax.t_unit
                       in
                    let uu____2285 =
                      let uu____2296 = FStar_Syntax_Syntax.as_arg res_t  in
                      let uu____2305 =
                        let uu____2316 = FStar_Syntax_Syntax.as_arg wp11  in
                        let uu____2325 =
                          let uu____2336 =
                            let uu____2345 =
                              let uu____2346 =
                                let uu____2347 =
                                  FStar_Syntax_Syntax.null_binder
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                [uu____2347]  in
                              FStar_Syntax_Util.abs uu____2346 wp2
                                (FStar_Pervasives_Native.Some
                                   (FStar_Syntax_Util.mk_residual_comp
                                      FStar_Parser_Const.effect_Tot_lid
                                      FStar_Pervasives_Native.None
                                      [FStar_Syntax_Syntax.TOTAL]))
                               in
                            FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                              uu____2345
                             in
                          [uu____2336]  in
                        uu____2316 :: uu____2325  in
                      uu____2296 :: uu____2305  in
                    uu____2268 :: uu____2285  in
                  uu____2239 :: uu____2257  in
                FStar_Syntax_Syntax.mk_Tm_app uu____2237 uu____2238  in
              uu____2232 FStar_Pervasives_Native.None
                wp2.FStar_Syntax_Syntax.pos
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____2436 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_2442  ->
              match uu___1_2442 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____2445 -> false))
       in
    if uu____2436
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_2457  ->
              match uu___2_2457 with
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
        let uu____2477 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____2477
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____2483 = destruct_comp c1  in
           match uu____2483 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let r = FStar_TypeChecker_Env.get_range env  in
               let pure_assume_wp =
                 let uu____2496 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assume_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____2496  in
               let pure_assume_wp1 =
                 let uu____2501 =
                   let uu____2506 =
                     let uu____2507 =
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula
                        in
                     [uu____2507]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____2506
                    in
                 uu____2501 FStar_Pervasives_Native.None r  in
               let w_wp =
                 lift_wp_and_bind_with env pure_assume_wp1 md u_res_t res_t
                   wp
                  in
               let uu____2541 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t w_wp uu____2541)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____2569 =
          let uu____2570 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____2570 with
          | (c,g_c) ->
              let uu____2581 =
                let uu____2582 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                   in
                if uu____2582
                then c
                else
                  (match f with
                   | FStar_TypeChecker_Common.Trivial  -> c
                   | FStar_TypeChecker_Common.NonTrivial f1 ->
                       weaken_comp env c f1)
                 in
              (uu____2581, g_c)
           in
        let uu____2588 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____2588 weaken
  
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
               let uu____2637 = destruct_comp c1  in
               match uu____2637 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let pure_assert_wp =
                     let uu____2649 =
                       FStar_Syntax_Syntax.lid_as_fv
                         FStar_Parser_Const.pure_assert_wp_lid
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____2649  in
                   let pure_assert_wp1 =
                     let uu____2654 =
                       let uu____2659 =
                         let uu____2660 =
                           let uu____2669 = label_opt env reason r f  in
                           FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                             uu____2669
                            in
                         [uu____2660]  in
                       FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp
                         uu____2659
                        in
                     uu____2654 FStar_Pervasives_Native.None r  in
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
            let uu____2740 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____2740
            then (lc, g0)
            else
              (let flags =
                 let uu____2752 =
                   let uu____2760 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____2760
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____2752 with
                 | (maybe_trivial_post,flags) ->
                     let uu____2790 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_2798  ->
                               match uu___3_2798 with
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
                               | uu____2801 -> []))
                        in
                     FStar_List.append flags uu____2790
                  in
               let strengthen uu____2811 =
                 let uu____2812 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____2812 with
                 | (c,g_c) ->
                     let uu____2823 =
                       if env.FStar_TypeChecker_Env.lax
                       then c
                       else
                         (let g01 =
                            FStar_TypeChecker_Rel.simplify_guard env g0  in
                          let uu____2828 =
                            FStar_TypeChecker_Env.guard_form g01  in
                          match uu____2828 with
                          | FStar_TypeChecker_Common.Trivial  -> c
                          | FStar_TypeChecker_Common.NonTrivial f ->
                              ((let uu____2831 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    FStar_Options.Extreme
                                   in
                                if uu____2831
                                then
                                  let uu____2835 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env e_for_debugging_only
                                     in
                                  let uu____2837 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env f
                                     in
                                  FStar_Util.print2
                                    "-------------Strengthening pre-condition of term %s with guard %s\n"
                                    uu____2835 uu____2837
                                else ());
                               strengthen_comp env reason c f flags))
                        in
                     (uu____2823, g_c)
                  in
               let uu____2842 =
                 let uu____2843 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____2843
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____2842,
                 (let uu___416_2845 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___416_2845.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___416_2845.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___416_2845.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_2854  ->
            match uu___4_2854 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____2858 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____2887 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____2887
          then e
          else
            (let uu____2894 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____2897 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____2897)
                in
             if uu____2894
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
          fun uu____2950  ->
            match uu____2950 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____2970 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____2970 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____2983 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____2983
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____2993 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____2993
                       then
                         let uu____2998 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____2998
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____3005 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____3005
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____3014 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____3014
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____3021 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____3021
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____3037 =
                  let uu____3038 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____3038
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____3046 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____3046, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____3049 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____3049 with
                     | (c1,g_c1) ->
                         let uu____3060 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____3060 with
                          | (c2,g_c2) ->
                              (debug1
                                 (fun uu____3080  ->
                                    let uu____3081 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____3083 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____3088 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____3081 uu____3083 uu____3088);
                               (let aux uu____3106 =
                                  let uu____3107 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____3107
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____3138
                                        ->
                                        let uu____3139 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____3139
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____3171 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____3171
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____3216 =
                                  let uu____3217 =
                                    let uu____3219 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____3219  in
                                  if uu____3217
                                  then
                                    let uu____3233 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____3233
                                     then
                                       FStar_Util.Inl
                                         (c2,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____3256 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____3256))
                                  else
                                    (let uu____3271 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____3271
                                     then
                                       let close1 x reason c =
                                         let x1 =
                                           let uu___486_3313 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___486_3313.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___486_3313.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           }  in
                                         let uu____3314 =
                                           let uu____3320 =
                                             close_comp_if_refinement_t env
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c
                                              in
                                           (uu____3320, reason)  in
                                         FStar_Util.Inl uu____3314  in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some
                                          e,FStar_Pervasives_Native.Some x)
                                           ->
                                           let uu____3356 =
                                             FStar_All.pipe_right c2
                                               (FStar_Syntax_Subst.subst_comp
                                                  [FStar_Syntax_Syntax.NT
                                                     (x, e)])
                                              in
                                           FStar_All.pipe_right uu____3356
                                             (close1 x "c1 Tot")
                                       | (uu____3370,FStar_Pervasives_Native.Some
                                          x) ->
                                           FStar_All.pipe_right c2
                                             (close1 x "c1 Tot only close")
                                       | (uu____3393,uu____3394) -> aux ()
                                     else
                                       (let uu____3409 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____3409
                                        then
                                          let uu____3422 =
                                            let uu____3428 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____3428, "both GTot")  in
                                          FStar_Util.Inl uu____3422
                                        else aux ()))
                                   in
                                let uu____3439 = try_simplify ()  in
                                match uu____3439 with
                                | FStar_Util.Inl (c,reason) ->
                                    (debug1
                                       (fun uu____3469  ->
                                          let uu____3470 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____3470);
                                     (let uu____3473 =
                                        FStar_TypeChecker_Env.conj_guard g_c1
                                          g_c2
                                         in
                                      (c, uu____3473)))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____3485  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_layered_bind c11 b1 c21 =
                                        let ct1 =
                                          FStar_TypeChecker_Env.unfold_effect_abbrev
                                            env c11
                                           in
                                        let ct2 =
                                          FStar_TypeChecker_Env.unfold_effect_abbrev
                                            env c21
                                           in
                                        let uu____3513 =
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
                                          let uu____3526 =
                                            FStar_TypeChecker_Env.monad_leq
                                              env
                                              c1_ed.FStar_Syntax_Syntax.mname
                                              c2_ed.FStar_Syntax_Syntax.mname
                                             in
                                          match uu____3526 with
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____3539 =
                                                FStar_TypeChecker_Env.monad_leq
                                                  env
                                                  c2_ed.FStar_Syntax_Syntax.mname
                                                  c1_ed.FStar_Syntax_Syntax.mname
                                                 in
                                              (match uu____3539 with
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
                                                   (ct2, c2_ed, ed, ct1,
                                                     c1_ed))
                                          | FStar_Pervasives_Native.Some ed
                                              -> (ct1, c1_ed, ed, ct2, c2_ed)
                                           in
                                        match uu____3513 with
                                        | (ct11,uu____3571,uu____3572,ct21,c2_ed)
                                            ->
                                            let uu____3575 =
                                              let uu____3580 =
                                                let uu____3585 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct11
                                                   in
                                                FStar_TypeChecker_Env.lift_to_layered_effect
                                                  env uu____3585
                                                  c2_ed.FStar_Syntax_Syntax.mname
                                                 in
                                              FStar_All.pipe_right uu____3580
                                                (fun uu____3598  ->
                                                   match uu____3598 with
                                                   | (c,g) ->
                                                       let uu____3609 =
                                                         FStar_Syntax_Util.comp_to_comp_typ
                                                           c
                                                          in
                                                       (uu____3609, g))
                                               in
                                            (match uu____3575 with
                                             | (ct12,g_lift) ->
                                                 let uu____3616 =
                                                   let uu____3627 =
                                                     FStar_List.hd
                                                       ct12.FStar_Syntax_Syntax.comp_univs
                                                      in
                                                   let uu____3628 =
                                                     FStar_List.map
                                                       FStar_Pervasives_Native.fst
                                                       ct12.FStar_Syntax_Syntax.effect_args
                                                      in
                                                   (uu____3627,
                                                     (ct12.FStar_Syntax_Syntax.result_typ),
                                                     uu____3628)
                                                    in
                                                 (match uu____3616 with
                                                  | (u1,t1,is1) ->
                                                      let uu____3662 =
                                                        let uu____3673 =
                                                          FStar_List.hd
                                                            ct21.FStar_Syntax_Syntax.comp_univs
                                                           in
                                                        let uu____3674 =
                                                          FStar_List.map
                                                            FStar_Pervasives_Native.fst
                                                            ct21.FStar_Syntax_Syntax.effect_args
                                                           in
                                                        (uu____3673,
                                                          (ct21.FStar_Syntax_Syntax.result_typ),
                                                          uu____3674)
                                                         in
                                                      (match uu____3662 with
                                                       | (u2,t2,is2) ->
                                                           let uu____3708 =
                                                             FStar_TypeChecker_Env.inst_tscheme_with
                                                               c2_ed.FStar_Syntax_Syntax.bind_wp
                                                               [u1; u2]
                                                              in
                                                           (match uu____3708
                                                            with
                                                            | (uu____3717,bind_t)
                                                                ->
                                                                let uu____3719
                                                                  =
                                                                  let uu____3732
                                                                    =
                                                                    let uu____3733
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    bind_t
                                                                     in
                                                                    uu____3733.FStar_Syntax_Syntax.n
                                                                     in
                                                                  match uu____3732
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____3770
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    FStar_All.pipe_right
                                                                    uu____3770
                                                                    (fun
                                                                    uu____3787
                                                                     ->
                                                                    match uu____3787
                                                                    with
                                                                    | 
                                                                    (bs1,c3)
                                                                    ->
                                                                    let uu____3798
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    c3
                                                                    FStar_Syntax_Util.comp_to_comp_typ
                                                                     in
                                                                    (bs1,
                                                                    uu____3798))
                                                                  | uu____3799
                                                                    ->
                                                                    let uu____3800
                                                                    =
                                                                    let uu____3802
                                                                    =
                                                                    let uu____3804
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____3804
                                                                    " is not an arrow"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "bind_t: "
                                                                    uu____3802
                                                                     in
                                                                    failwith
                                                                    uu____3800
                                                                   in
                                                                (match uu____3719
                                                                 with
                                                                 | (bind_bs,bind_ct)
                                                                    ->
                                                                    let uu____3842
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
                                                                    let uu____3953
                                                                    =
                                                                    let uu____3980
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs) -
                                                                    (Prims.of_int (2)))
                                                                    bs  in
                                                                    FStar_All.pipe_right
                                                                    uu____3980
                                                                    (fun
                                                                    uu____4065
                                                                     ->
                                                                    match uu____4065
                                                                    with
                                                                    | 
                                                                    (l1,l2)
                                                                    ->
                                                                    let uu____4146
                                                                    =
                                                                    FStar_List.hd
                                                                    l2  in
                                                                    let uu____4159
                                                                    =
                                                                    let uu____4166
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                    FStar_List.hd
                                                                    uu____4166
                                                                     in
                                                                    (l1,
                                                                    uu____4146,
                                                                    uu____4159))
                                                                     in
                                                                    (match uu____3953
                                                                    with
                                                                    | 
                                                                    (rest_bs,f_b,g_b)
                                                                    ->
                                                                    (a_b,
                                                                    b_b,
                                                                    rest_bs,
                                                                    f_b, g_b))
                                                                    | 
                                                                    uu____4308
                                                                    ->
                                                                    let uu____4317
                                                                    =
                                                                    let uu____4319
                                                                    =
                                                                    let uu____4321
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____4321
                                                                    " does not have enough binders"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "bind_t: "
                                                                    uu____4319
                                                                     in
                                                                    failwith
                                                                    uu____4317
                                                                     in
                                                                    (match uu____3842
                                                                    with
                                                                    | 
                                                                    (a_b,b_b,rest_bs,f_b,g_b)
                                                                    ->
                                                                    let rest_bs1
                                                                    =
                                                                    let uu____4417
                                                                    =
                                                                    let uu____4420
                                                                    =
                                                                    let uu____4421
                                                                    =
                                                                    let uu____4428
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    a_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    (uu____4428,
                                                                    t1)  in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4421
                                                                     in
                                                                    let uu____4439
                                                                    =
                                                                    let uu____4442
                                                                    =
                                                                    let uu____4443
                                                                    =
                                                                    let uu____4450
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    b_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    (uu____4450,
                                                                    t2)  in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4443
                                                                     in
                                                                    [uu____4442]
                                                                     in
                                                                    uu____4420
                                                                    ::
                                                                    uu____4439
                                                                     in
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    uu____4417
                                                                    rest_bs
                                                                     in
                                                                    let uu____4461
                                                                    =
                                                                    let uu____4468
                                                                    =
                                                                    let uu____4469
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    bind_ct.FStar_Syntax_Syntax.result_typ
                                                                     in
                                                                    uu____4469.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____4468
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____4478,uu____4479::is)
                                                                    ->
                                                                    let uu____4521
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    is  in
                                                                    ((bind_ct.FStar_Syntax_Syntax.comp_univs),
                                                                    uu____4521)
                                                                    | 
                                                                    uu____4538
                                                                    ->
                                                                    let uu____4539
                                                                    =
                                                                    let uu____4541
                                                                    =
                                                                    let uu____4543
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____4543
                                                                    " does not have repr return type"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "bind_t: "
                                                                    uu____4541
                                                                     in
                                                                    failwith
                                                                    uu____4539
                                                                     in
                                                                    (match uu____4461
                                                                    with
                                                                    | 
                                                                    (u_m,is)
                                                                    ->
                                                                    let uu____4563
                                                                    =
                                                                    let uu____4572
                                                                    =
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____4611
                                                                     ->
                                                                    fun b2 
                                                                    ->
                                                                    match uu____4611
                                                                    with
                                                                    | 
                                                                    (substs,is_uvars,g)
                                                                    ->
                                                                    let sort
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    substs
                                                                    (FStar_Pervasives_Native.fst
                                                                    b2).FStar_Syntax_Syntax.sort
                                                                     in
                                                                    let uu____4653
                                                                    =
                                                                    FStar_TypeChecker_Env.new_implicit_var_aux
                                                                    ""
                                                                    FStar_Range.dummyRange
                                                                    env sort
                                                                    FStar_Syntax_Syntax.Strict
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (match uu____4653
                                                                    with
                                                                    | 
                                                                    (t,uu____4682,g_t)
                                                                    ->
                                                                    let uu____4696
                                                                    =
                                                                    let uu____4699
                                                                    =
                                                                    let uu____4702
                                                                    =
                                                                    let uu____4703
                                                                    =
                                                                    let uu____4710
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    b2
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    (uu____4710,
                                                                    t)  in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4703
                                                                     in
                                                                    [uu____4702]
                                                                     in
                                                                    FStar_List.append
                                                                    substs
                                                                    uu____4699
                                                                     in
                                                                    let uu____4721
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g g_t  in
                                                                    (uu____4696,
                                                                    (FStar_List.append
                                                                    is_uvars
                                                                    [t]),
                                                                    uu____4721)))
                                                                    ([], [],
                                                                    FStar_TypeChecker_Common.trivial_guard)
                                                                    rest_bs1
                                                                     in
                                                                    match uu____4572
                                                                    with
                                                                    | 
                                                                    (uu____4738,rest_bs_uvars,g)
                                                                    ->
                                                                    (rest_bs_uvars,
                                                                    g)  in
                                                                    (match uu____4563
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
                                                                    let uu____4791
                                                                    =
                                                                    let uu____4798
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    b2
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    (uu____4798,
                                                                    t)  in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4791)
                                                                    (a_b ::
                                                                    b_b ::
                                                                    rest_bs1)
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
                                                                    let uu____4831
                                                                    =
                                                                    let uu____4832
                                                                    =
                                                                    let uu____4835
                                                                    =
                                                                    let uu____4836
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    f_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    uu____4836.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_Syntax_Subst.compress
                                                                    uu____4835
                                                                     in
                                                                    uu____4832.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____4831
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____4847,uu____4848::is4)
                                                                    ->
                                                                    let uu____4890
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is4
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4890
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1))
                                                                    | 
                                                                    uu____4923
                                                                    ->
                                                                    let uu____4924
                                                                    =
                                                                    let uu____4926
                                                                    =
                                                                    let uu____4928
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____4928
                                                                    " is not a repr type"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "Type of f in bind_t:"
                                                                    uu____4926
                                                                     in
                                                                    failwith
                                                                    uu____4924
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
                                                                    let uu____4951
                                                                    =
                                                                    let uu____4952
                                                                    =
                                                                    let uu____4955
                                                                    =
                                                                    let uu____4956
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    g_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    uu____4956.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_Syntax_Subst.compress
                                                                    uu____4955
                                                                     in
                                                                    uu____4952.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____4951
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____4989
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____4989
                                                                    with
                                                                    | 
                                                                    (bs1,c3)
                                                                    ->
                                                                    let bs_subst
                                                                    =
                                                                    let uu____4999
                                                                    =
                                                                    let uu____5006
                                                                    =
                                                                    let uu____5007
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____5007
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____5028
                                                                    =
                                                                    let uu____5031
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5031
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____5006,
                                                                    uu____5028)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4999
                                                                     in
                                                                    let c4 =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c3  in
                                                                    let uu____5045
                                                                    =
                                                                    let uu____5046
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c4)  in
                                                                    uu____5046.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5045
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____5051,uu____5052::is4)
                                                                    ->
                                                                    let uu____5094
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is4
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5094
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1))
                                                                    | 
                                                                    uu____5119
                                                                    ->
                                                                    let uu____5120
                                                                    =
                                                                    let uu____5122
                                                                    =
                                                                    let uu____5124
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____5124
                                                                    " is not a repr type"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "Type of g in bind_t:"
                                                                    uu____5122
                                                                     in
                                                                    failwith
                                                                    uu____5120))
                                                                    | 
                                                                    uu____5130
                                                                    ->
                                                                    let uu____5131
                                                                    =
                                                                    let uu____5133
                                                                    =
                                                                    let uu____5135
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____5135
                                                                    " is not a arrow type"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "Type of g in bind_t:"
                                                                    uu____5133
                                                                     in
                                                                    failwith
                                                                    uu____5131
                                                                     in
                                                                    let g =
                                                                    let uu____5142
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
                                                                    let uu____5150
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env i1
                                                                    f_i1  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____5150)
                                                                    uu____5142
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
                                                                    let uu____5159
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env i1
                                                                    g_i1  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g1
                                                                    uu____5159)
                                                                    g is2
                                                                    g_sort_is
                                                                     in
                                                                    let uu____5160
                                                                    =
                                                                    let uu____5161
                                                                    =
                                                                    let uu____5162
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
                                                                    uu____5162;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    uu____5161
                                                                     in
                                                                    let uu____5181
                                                                    =
                                                                    let uu____5182
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_c1 g_c2
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g1
                                                                    uu____5182
                                                                     in
                                                                    (uu____5160,
                                                                    uu____5181)))))))))
                                         in
                                      let mk_bind c11 b1 c21 =
                                        let uu____5207 =
                                          lift_and_destruct env c11 c21  in
                                        match uu____5207 with
                                        | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2))
                                            ->
                                            let bs =
                                              match b1 with
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____5264 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      t1
                                                     in
                                                  [uu____5264]
                                              | FStar_Pervasives_Native.Some
                                                  x ->
                                                  let uu____5284 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____5284]
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
                                              let uu____5331 =
                                                FStar_Syntax_Syntax.as_arg
                                                  r11
                                                 in
                                              let uu____5340 =
                                                let uu____5351 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1
                                                   in
                                                let uu____5360 =
                                                  let uu____5371 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      t2
                                                     in
                                                  let uu____5380 =
                                                    let uu____5391 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        wp1
                                                       in
                                                    let uu____5400 =
                                                      let uu____5411 =
                                                        let uu____5420 =
                                                          mk_lam wp2  in
                                                        FStar_Syntax_Syntax.as_arg
                                                          uu____5420
                                                         in
                                                      [uu____5411]  in
                                                    uu____5391 :: uu____5400
                                                     in
                                                  uu____5371 :: uu____5380
                                                   in
                                                uu____5351 :: uu____5360  in
                                              uu____5331 :: uu____5340  in
                                            let wp =
                                              let uu____5472 =
                                                let uu____5477 =
                                                  FStar_TypeChecker_Env.inst_effect_fun_with
                                                    [u_t1; u_t2] env md
                                                    md.FStar_Syntax_Syntax.bind_wp
                                                   in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____5477 wp_args
                                                 in
                                              uu____5472
                                                FStar_Pervasives_Native.None
                                                t2.FStar_Syntax_Syntax.pos
                                               in
                                            let uu____5478 =
                                              mk_comp md u_t2 t2 wp
                                                bind_flags
                                               in
                                            let uu____5479 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g_c1 g_c2
                                               in
                                            (uu____5478, uu____5479)
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
                                        let uu____5506 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____5506 with
                                        | (m,uu____5518,lift2) ->
                                            let c23 =
                                              let uu____5521 =
                                                lift_comp c22 m lift2  in
                                              FStar_Syntax_Syntax.mk_Comp
                                                uu____5521
                                               in
                                            let uu____5522 =
                                              destruct_comp c12  in
                                            (match uu____5522 with
                                             | (u1,t1,wp1) ->
                                                 let md_pure_or_ghost =
                                                   FStar_TypeChecker_Env.get_effect_decl
                                                     env
                                                     c12.FStar_Syntax_Syntax.effect_name
                                                    in
                                                 let vc1 =
                                                   let uu____5540 =
                                                     let uu____5545 =
                                                       let uu____5546 =
                                                         FStar_All.pipe_right
                                                           md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                                           FStar_Util.must
                                                          in
                                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                                         [u1] env
                                                         md_pure_or_ghost
                                                         uu____5546
                                                        in
                                                     let uu____5549 =
                                                       let uu____5550 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           t1
                                                          in
                                                       let uu____5559 =
                                                         let uu____5570 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             wp1
                                                            in
                                                         [uu____5570]  in
                                                       uu____5550 ::
                                                         uu____5559
                                                        in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       uu____5545 uu____5549
                                                      in
                                                   uu____5540
                                                     FStar_Pervasives_Native.None
                                                     r1
                                                    in
                                                 let uu____5603 =
                                                   strengthen_comp env
                                                     FStar_Pervasives_Native.None
                                                     c23 vc1 bind_flags
                                                    in
                                                 let uu____5608 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 g_c2
                                                    in
                                                 (uu____5603, uu____5608))
                                         in
                                      let uu____5609 =
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
                                      if uu____5609
                                      then mk_layered_bind c1 b c2
                                      else
                                        (let c1_typ =
                                           FStar_TypeChecker_Env.unfold_effect_abbrev
                                             env c1
                                            in
                                         let uu____5621 =
                                           destruct_comp c1_typ  in
                                         match uu____5621 with
                                         | (u_res_t1,res_t1,uu____5634) ->
                                             let uu____5635 =
                                               (FStar_Option.isSome b) &&
                                                 (should_return env e1opt
                                                    lc11)
                                                in
                                             if uu____5635
                                             then
                                               let e1 =
                                                 FStar_Option.get e1opt  in
                                               let x = FStar_Option.get b  in
                                               let uu____5644 =
                                                 FStar_Syntax_Util.is_partial_return
                                                   c1
                                                  in
                                               (if uu____5644
                                                then
                                                  (debug1
                                                     (fun uu____5658  ->
                                                        let uu____5659 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____5661 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case a): Substituting %s for %s"
                                                          uu____5659
                                                          uu____5661);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    mk_bind c1 b c21))
                                                else
                                                  (let uu____5669 =
                                                     ((FStar_Options.vcgen_optimize_bind_as_seq
                                                         ())
                                                        &&
                                                        (lcomp_has_trivial_postcondition
                                                           lc11))
                                                       &&
                                                       (let uu____5672 =
                                                          FStar_TypeChecker_Env.try_lookup_lid
                                                            env
                                                            FStar_Parser_Const.with_type_lid
                                                           in
                                                        FStar_Option.isSome
                                                          uu____5672)
                                                      in
                                                   if uu____5669
                                                   then
                                                     let e1' =
                                                       let uu____5697 =
                                                         FStar_Options.vcgen_decorate_with_type
                                                           ()
                                                          in
                                                       if uu____5697
                                                       then
                                                         FStar_Syntax_Util.mk_with_type
                                                           u_res_t1 res_t1 e1
                                                       else e1  in
                                                     (debug1
                                                        (fun uu____5709  ->
                                                           let uu____5710 =
                                                             FStar_TypeChecker_Normalize.term_to_string
                                                               env e1'
                                                              in
                                                           let uu____5712 =
                                                             FStar_Syntax_Print.bv_to_string
                                                               x
                                                              in
                                                           FStar_Util.print2
                                                             "(3) bind (case b): Substituting %s for %s"
                                                             uu____5710
                                                             uu____5712);
                                                      (let c21 =
                                                         FStar_Syntax_Subst.subst_comp
                                                           [FStar_Syntax_Syntax.NT
                                                              (x, e1')] c2
                                                          in
                                                       mk_seq c1 b c21))
                                                   else
                                                     (debug1
                                                        (fun uu____5727  ->
                                                           let uu____5728 =
                                                             FStar_TypeChecker_Normalize.term_to_string
                                                               env e1
                                                              in
                                                           let uu____5730 =
                                                             FStar_Syntax_Print.bv_to_string
                                                               x
                                                              in
                                                           FStar_Util.print2
                                                             "(3) bind (case c): Adding equality %s = %s"
                                                             uu____5728
                                                             uu____5730);
                                                      (let c21 =
                                                         FStar_Syntax_Subst.subst_comp
                                                           [FStar_Syntax_Syntax.NT
                                                              (x, e1)] c2
                                                          in
                                                       let x_eq_e =
                                                         let uu____5737 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_Syntax_Util.mk_eq2
                                                           u_res_t1 res_t1 e1
                                                           uu____5737
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
      | uu____5755 -> g2
  
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
            (let uu____5779 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____5779)
           in
        let flags =
          if should_return1
          then
            let uu____5787 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____5787
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____5805 =
          let uu____5806 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5806 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____5819 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____5819
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____5827 =
                  let uu____5829 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____5829  in
                (if uu____5827
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___747_5838 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___747_5838.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___747_5838.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___747_5838.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____5839 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____5839, g_c)
                 else
                   (let uu____5842 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____5842, g_c)))
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
                   let uu____5853 =
                     let uu____5854 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____5854
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____5853
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____5857 =
                   let uu____5862 =
                     let uu____5863 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____5863
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____5862  in
                 match uu____5857 with
                 | (bind_c,g_bind) ->
                     let uu____5872 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____5873 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____5872, uu____5873))
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
            fun uu____5909  ->
              match uu____5909 with
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
                    let uu____5921 =
                      ((let uu____5925 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____5925) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____5921
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____5943 =
        let uu____5944 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____5944  in
      FStar_Syntax_Syntax.fvar uu____5943 FStar_Syntax_Syntax.delta_constant
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
               fun uu____6014  ->
                 match uu____6014 with
                 | (uu____6028,eff_label,uu____6030,uu____6031) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____6044 =
          let uu____6052 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____6090  ->
                    match uu____6090 with
                    | (uu____6105,uu____6106,flags,uu____6108) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_6125  ->
                                match uu___5_6125 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____6128 -> false))))
             in
          if uu____6052
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____6044 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____6165 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____6167 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____6167
              then
                let uu____6174 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                   in
                (uu____6174, FStar_TypeChecker_Env.trivial_guard)
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____6213 =
                     FStar_Syntax_Util.get_match_with_close_wps
                       md.FStar_Syntax_Syntax.match_wps
                      in
                   match uu____6213 with
                   | (if_then_else1,uu____6223,uu____6224) ->
                       let uu____6225 =
                         FStar_Range.union_ranges
                           wp_t.FStar_Syntax_Syntax.pos
                           wp_e.FStar_Syntax_Syntax.pos
                          in
                       let uu____6226 =
                         let uu____6231 =
                           FStar_TypeChecker_Env.inst_effect_fun_with
                             [u_res_t] env md if_then_else1
                            in
                         let uu____6232 =
                           let uu____6233 = FStar_Syntax_Syntax.as_arg res_t1
                              in
                           let uu____6242 =
                             let uu____6253 = FStar_Syntax_Syntax.as_arg g
                                in
                             let uu____6262 =
                               let uu____6273 =
                                 FStar_Syntax_Syntax.as_arg wp_t  in
                               let uu____6282 =
                                 let uu____6293 =
                                   FStar_Syntax_Syntax.as_arg wp_e  in
                                 [uu____6293]  in
                               uu____6273 :: uu____6282  in
                             uu____6253 :: uu____6262  in
                           uu____6233 :: uu____6242  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____6231 uu____6232
                          in
                       uu____6226 FStar_Pervasives_Native.None uu____6225
                    in
                 let default_case =
                   let post_k =
                     let uu____6346 =
                       let uu____6355 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____6355]  in
                     let uu____6374 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6346 uu____6374  in
                   let kwp =
                     let uu____6380 =
                       let uu____6389 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____6389]  in
                     let uu____6408 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6380 uu____6408  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____6415 =
                       let uu____6416 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____6416]  in
                     let uu____6435 =
                       let uu____6438 =
                         let uu____6445 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____6445
                          in
                       let uu____6446 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____6438 uu____6446  in
                     FStar_Syntax_Util.abs uu____6415 uu____6435
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
                   let uu____6470 =
                     should_not_inline_whole_match ||
                       (let uu____6473 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____6473)
                      in
                   if uu____6470 then cthen true else cthen false  in
                 let uu____6480 =
                   FStar_List.fold_right
                     (fun uu____6526  ->
                        fun uu____6527  ->
                          match (uu____6526, uu____6527) with
                          | ((g,eff_label,uu____6569,cthen),(celse,g_comp))
                              ->
                              let uu____6603 =
                                let uu____6608 = maybe_return eff_label cthen
                                   in
                                FStar_TypeChecker_Common.lcomp_comp
                                  uu____6608
                                 in
                              (match uu____6603 with
                               | (cthen1,gthen) ->
                                   let uu____6615 =
                                     lift_and_destruct env cthen1 celse  in
                                   (match uu____6615 with
                                    | ((md,uu____6645,uu____6646),(uu____6647,uu____6648,wp_then),
                                       (uu____6650,uu____6651,wp_else)) ->
                                        let uu____6671 =
                                          let uu____6672 =
                                            ifthenelse md res_t g wp_then
                                              wp_else
                                             in
                                          mk_comp md u_res_t res_t uu____6672
                                            []
                                           in
                                        let uu____6673 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_comp gthen
                                           in
                                        (uu____6671, uu____6673)))) lcases
                     (default_case, FStar_TypeChecker_Env.trivial_guard)
                    in
                 match uu____6480 with
                 | (comp,g_comp) ->
                     (match lcases with
                      | [] -> (comp, g_comp)
                      | uu____6698::[] -> (comp, g_comp)
                      | uu____6741 ->
                          let comp1 =
                            FStar_TypeChecker_Env.comp_to_comp_typ env comp
                             in
                          let md =
                            FStar_TypeChecker_Env.get_effect_decl env
                              comp1.FStar_Syntax_Syntax.effect_name
                             in
                          let uu____6760 = destruct_comp comp1  in
                          (match uu____6760 with
                           | (uu____6771,uu____6772,wp) ->
                               let uu____6774 =
                                 FStar_Syntax_Util.get_match_with_close_wps
                                   md.FStar_Syntax_Syntax.match_wps
                                  in
                               (match uu____6774 with
                                | (uu____6785,ite_wp,uu____6787) ->
                                    let wp1 =
                                      let uu____6791 =
                                        let uu____6796 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [u_res_t] env md ite_wp
                                           in
                                        let uu____6797 =
                                          let uu____6798 =
                                            FStar_Syntax_Syntax.as_arg res_t
                                             in
                                          let uu____6807 =
                                            let uu____6818 =
                                              FStar_Syntax_Syntax.as_arg wp
                                               in
                                            [uu____6818]  in
                                          uu____6798 :: uu____6807  in
                                        FStar_Syntax_Syntax.mk_Tm_app
                                          uu____6796 uu____6797
                                         in
                                      uu____6791 FStar_Pervasives_Native.None
                                        wp.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____6851 =
                                      mk_comp md u_res_t res_t wp1
                                        bind_cases_flags
                                       in
                                    (uu____6851, g_comp)))))
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
          let uu____6885 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____6885 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____6901 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____6907 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____6901 uu____6907
              else
                (let uu____6916 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____6922 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____6916 uu____6922)
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
          let uu____6947 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____6947
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____6950 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____6950
        then u_res
        else
          (let is_total =
             let uu____6957 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____6957
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____6968 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____6968 with
              | FStar_Pervasives_Native.None  ->
                  let uu____6971 =
                    let uu____6977 =
                      let uu____6979 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____6979
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____6977)
                     in
                  FStar_Errors.raise_error uu____6971
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
      let uu____7003 = destruct_comp ct  in
      match uu____7003 with
      | (u_t,t,wp) ->
          let vc =
            let uu____7022 = FStar_TypeChecker_Env.get_range env  in
            let uu____7023 =
              let uu____7028 =
                let uu____7029 =
                  FStar_All.pipe_right md.FStar_Syntax_Syntax.trivial
                    FStar_Util.must
                   in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____7029
                 in
              let uu____7032 =
                let uu____7033 = FStar_Syntax_Syntax.as_arg t  in
                let uu____7042 =
                  let uu____7053 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____7053]  in
                uu____7033 :: uu____7042  in
              FStar_Syntax_Syntax.mk_Tm_app uu____7028 uu____7032  in
            uu____7023 FStar_Pervasives_Native.None uu____7022  in
          let uu____7086 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____7086)
  
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
               let uu____7127 =
                 let uu____7128 = FStar_Syntax_Subst.compress t2  in
                 uu____7128.FStar_Syntax_Syntax.n  in
               match uu____7127 with
               | FStar_Syntax_Syntax.Tm_type uu____7132 -> true
               | uu____7134 -> false  in
             let uu____7136 =
               let uu____7137 =
                 FStar_Syntax_Util.unrefine
                   lc.FStar_TypeChecker_Common.res_typ
                  in
               uu____7137.FStar_Syntax_Syntax.n  in
             match uu____7136 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____7145 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____7155 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____7155
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____7158 =
                     let uu____7159 =
                       let uu____7160 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____7160
                        in
                     (FStar_Pervasives_Native.None, uu____7159)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____7158
                    in
                 let e1 =
                   let uu____7166 =
                     let uu____7171 =
                       let uu____7172 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____7172]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____7171  in
                   uu____7166 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____7197 -> (e, lc))
  
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
          (let uu____7232 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____7232
           then
             let uu____7235 = FStar_Syntax_Print.term_to_string e  in
             let uu____7237 = FStar_TypeChecker_Common.lcomp_to_string lc  in
             let uu____7239 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____7235 uu____7237 uu____7239
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____7249 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____7249 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____7274 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____7300 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____7300, false)
             else
               (let uu____7310 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____7310, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____7323) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____7335 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____7335
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___930_7351 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___930_7351.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___930_7351.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___930_7351.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____7358 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____7358 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____7374 =
                      let uu____7375 = FStar_TypeChecker_Common.lcomp_comp lc
                         in
                      match uu____7375 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____7395 =
                            let uu____7397 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____7397 = FStar_Syntax_Util.Equal  in
                          if uu____7395
                          then
                            ((let uu____7404 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____7404
                              then
                                let uu____7408 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____7410 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____7408 uu____7410
                              else ());
                             (let uu____7415 = set_result_typ1 c  in
                              (uu____7415, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____7422 ->
                                   true
                               | uu____7430 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____7439 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____7439
                                  in
                               let lc1 =
                                 let uu____7441 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____7442 =
                                   let uu____7443 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____7443)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____7441 uu____7442
                                  in
                               ((let uu____7447 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____7447
                                 then
                                   let uu____7451 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____7453 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____7455 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____7457 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____7451 uu____7453 uu____7455
                                     uu____7457
                                 else ());
                                (let uu____7462 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____7462 with
                                 | (c1,g_lc) ->
                                     let uu____7473 = set_result_typ1 c1  in
                                     let uu____7474 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____7473, uu____7474)))
                             else
                               ((let uu____7478 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____7478
                                 then
                                   let uu____7482 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____7484 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____7482 uu____7484
                                 else ());
                                (let uu____7489 = set_result_typ1 c  in
                                 (uu____7489, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___967_7493 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___967_7493.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___967_7493.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___967_7493.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____7503 =
                      let uu____7504 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____7504
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____7514 =
                           let uu____7515 = FStar_Syntax_Subst.compress f1
                              in
                           uu____7515.FStar_Syntax_Syntax.n  in
                         match uu____7514 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____7522,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____7524;
                                           FStar_Syntax_Syntax.vars =
                                             uu____7525;_},uu____7526)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___983_7552 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___983_7552.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___983_7552.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___983_7552.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____7553 ->
                             let uu____7554 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____7554 with
                              | (c,g_c) ->
                                  ((let uu____7566 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____7566
                                    then
                                      let uu____7570 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____7572 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____7574 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____7576 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____7570 uu____7572 uu____7574
                                        uu____7576
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
                                        let uu____7589 =
                                          let uu____7594 =
                                            let uu____7595 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____7595]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____7594
                                           in
                                        uu____7589
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____7622 =
                                      let uu____7627 =
                                        FStar_All.pipe_left
                                          (fun _7648  ->
                                             FStar_Pervasives_Native.Some
                                               _7648)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____7649 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____7650 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____7651 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____7627
                                        uu____7649 e uu____7650 uu____7651
                                       in
                                    match uu____7622 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1001_7659 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1001_7659.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1001_7659.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____7661 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____7661
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____7664 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____7664 with
                                         | (c2,g_lc) ->
                                             ((let uu____7676 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____7676
                                               then
                                                 let uu____7680 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____7680
                                               else ());
                                              (let uu____7685 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____7685))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_7694  ->
                              match uu___6_7694 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____7697 -> []))
                       in
                    let lc1 =
                      let uu____7699 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____7699 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1017_7701 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1017_7701.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1017_7701.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1017_7701.FStar_TypeChecker_Common.implicits)
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
        let uu____7737 =
          let uu____7740 =
            let uu____7745 =
              let uu____7746 =
                let uu____7755 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____7755  in
              [uu____7746]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____7745  in
          uu____7740 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____7737  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____7778 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____7778
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____7797 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____7813 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____7830 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____7830
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____7846)::(ens,uu____7848)::uu____7849 ->
                    let uu____7892 =
                      let uu____7895 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____7895  in
                    let uu____7896 =
                      let uu____7897 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____7897  in
                    (uu____7892, uu____7896)
                | uu____7900 ->
                    let uu____7911 =
                      let uu____7917 =
                        let uu____7919 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____7919
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____7917)
                       in
                    FStar_Errors.raise_error uu____7911
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____7939)::uu____7940 ->
                    let uu____7967 =
                      let uu____7972 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____7972
                       in
                    (match uu____7967 with
                     | (us_r,uu____8004) ->
                         let uu____8005 =
                           let uu____8010 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____8010
                            in
                         (match uu____8005 with
                          | (us_e,uu____8042) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____8045 =
                                  let uu____8046 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8046
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8045
                                  us_r
                                 in
                              let as_ens =
                                let uu____8048 =
                                  let uu____8049 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8049
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8048
                                  us_e
                                 in
                              let req =
                                let uu____8053 =
                                  let uu____8058 =
                                    let uu____8059 =
                                      let uu____8070 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8070]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8059
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____8058
                                   in
                                uu____8053 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____8110 =
                                  let uu____8115 =
                                    let uu____8116 =
                                      let uu____8127 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8127]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8116
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____8115
                                   in
                                uu____8110 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____8164 =
                                let uu____8167 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____8167  in
                              let uu____8168 =
                                let uu____8169 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____8169  in
                              (uu____8164, uu____8168)))
                | uu____8172 -> failwith "Impossible"))
  
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
      (let uu____8206 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____8206
       then
         let uu____8211 = FStar_Syntax_Print.term_to_string tm  in
         let uu____8213 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____8211 uu____8213
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
        (let uu____8267 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____8267
         then
           let uu____8272 = FStar_Syntax_Print.term_to_string tm  in
           let uu____8274 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____8272
             uu____8274
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____8285 =
      let uu____8287 =
        let uu____8288 = FStar_Syntax_Subst.compress t  in
        uu____8288.FStar_Syntax_Syntax.n  in
      match uu____8287 with
      | FStar_Syntax_Syntax.Tm_app uu____8292 -> false
      | uu____8310 -> true  in
    if uu____8285
    then t
    else
      (let uu____8315 = FStar_Syntax_Util.head_and_args t  in
       match uu____8315 with
       | (head1,args) ->
           let uu____8358 =
             let uu____8360 =
               let uu____8361 = FStar_Syntax_Subst.compress head1  in
               uu____8361.FStar_Syntax_Syntax.n  in
             match uu____8360 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____8366 -> false  in
           if uu____8358
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____8398 ->
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
          ((let uu____8445 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____8445
            then
              let uu____8448 = FStar_Syntax_Print.term_to_string e  in
              let uu____8450 = FStar_Syntax_Print.term_to_string t  in
              let uu____8452 =
                let uu____8454 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____8454
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____8448 uu____8450 uu____8452
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____8467 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____8467 with
              | (formals,uu____8483) ->
                  let n_implicits =
                    let uu____8505 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____8583  ->
                              match uu____8583 with
                              | (uu____8591,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____8598 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____8598 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____8505 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____8723 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____8723 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____8737 =
                      let uu____8743 =
                        let uu____8745 = FStar_Util.string_of_int n_expected
                           in
                        let uu____8747 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____8749 = FStar_Util.string_of_int n_available
                           in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____8745 uu____8747 uu____8749
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____8743)
                       in
                    let uu____8753 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____8737 uu____8753
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_8771 =
              match uu___7_8771 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____8814 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____8814 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _8945,uu____8932) when
                           _8945 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____8978,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Implicit
                                      uu____8980))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____9014 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____9014 with
                            | (v1,uu____9055,g) ->
                                ((let uu____9070 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____9070
                                  then
                                    let uu____9073 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____9073
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____9083 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____9083 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____9176 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____9176))))
                       | (uu____9203,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____9240 =
                             let uu____9253 =
                               let uu____9260 =
                                 let uu____9265 = FStar_Dyn.mkdyn env  in
                                 (uu____9265, tau)  in
                               FStar_Pervasives_Native.Some uu____9260  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____9253
                              in
                           (match uu____9240 with
                            | (v1,uu____9298,g) ->
                                ((let uu____9313 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____9313
                                  then
                                    let uu____9316 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____9316
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____9326 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____9326 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____9419 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____9419))))
                       | (uu____9446,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____9494 =
                       let uu____9521 = inst_n_binders t1  in
                       aux [] uu____9521 bs1  in
                     (match uu____9494 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____9593) -> (e, torig, guard)
                           | (uu____9624,[]) when
                               let uu____9655 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____9655 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____9657 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____9685 ->
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
            | uu____9698 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____9710 =
      let uu____9714 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____9714
        (FStar_List.map
           (fun u  ->
              let uu____9726 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____9726 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____9710 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____9754 = FStar_Util.set_is_empty x  in
      if uu____9754
      then []
      else
        (let s =
           let uu____9772 =
             let uu____9775 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____9775  in
           FStar_All.pipe_right uu____9772 FStar_Util.set_elements  in
         (let uu____9791 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____9791
          then
            let uu____9796 =
              let uu____9798 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____9798  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____9796
          else ());
         (let r =
            let uu____9807 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____9807  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____9846 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____9846
                     then
                       let uu____9851 =
                         let uu____9853 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____9853
                          in
                       let uu____9857 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____9859 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____9851 uu____9857 uu____9859
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
        let uu____9889 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____9889 FStar_Util.set_elements  in
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
        | ([],uu____9928) -> generalized_univ_names
        | (uu____9935,[]) -> explicit_univ_names
        | uu____9942 ->
            let uu____9951 =
              let uu____9957 =
                let uu____9959 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____9959
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____9957)
               in
            FStar_Errors.raise_error uu____9951 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____9981 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____9981
       then
         let uu____9986 = FStar_Syntax_Print.term_to_string t  in
         let uu____9988 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____9986 uu____9988
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____9997 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____9997
        then
          let uu____10002 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____10002
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____10011 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____10011
         then
           let uu____10016 = FStar_Syntax_Print.term_to_string t  in
           let uu____10018 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____10016 uu____10018
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
        let uu____10102 =
          let uu____10104 =
            FStar_Util.for_all
              (fun uu____10118  ->
                 match uu____10118 with
                 | (uu____10128,uu____10129,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____10104  in
        if uu____10102
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____10181 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____10181
              then
                let uu____10184 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____10184
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____10191 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____10191
               then
                 let uu____10194 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____10194
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____10212 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____10212 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____10246 =
             match uu____10246 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____10283 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____10283
                   then
                     let uu____10288 =
                       let uu____10290 =
                         let uu____10294 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____10294
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____10290
                         (FStar_String.concat ", ")
                        in
                     let uu____10342 =
                       let uu____10344 =
                         let uu____10348 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____10348
                           (FStar_List.map
                              (fun u  ->
                                 let uu____10361 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____10363 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____10361
                                   uu____10363))
                          in
                       FStar_All.pipe_right uu____10344
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____10288
                       uu____10342
                   else ());
                  (let univs2 =
                     let uu____10377 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____10389 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____10389) univs1
                       uu____10377
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____10396 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____10396
                    then
                      let uu____10401 =
                        let uu____10403 =
                          let uu____10407 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____10407
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____10403
                          (FStar_String.concat ", ")
                         in
                      let uu____10455 =
                        let uu____10457 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____10471 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____10473 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____10471
                                    uu____10473))
                           in
                        FStar_All.pipe_right uu____10457
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____10401 uu____10455
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____10494 =
             let uu____10511 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____10511  in
           match uu____10494 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____10601 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____10601
                 then ()
                 else
                   (let uu____10606 = lec_hd  in
                    match uu____10606 with
                    | (lb1,uu____10614,uu____10615) ->
                        let uu____10616 = lec2  in
                        (match uu____10616 with
                         | (lb2,uu____10624,uu____10625) ->
                             let msg =
                               let uu____10628 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10630 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____10628 uu____10630
                                in
                             let uu____10633 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____10633))
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
                 let uu____10701 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____10701
                 then ()
                 else
                   (let uu____10706 = lec_hd  in
                    match uu____10706 with
                    | (lb1,uu____10714,uu____10715) ->
                        let uu____10716 = lec2  in
                        (match uu____10716 with
                         | (lb2,uu____10724,uu____10725) ->
                             let msg =
                               let uu____10728 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10730 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____10728 uu____10730
                                in
                             let uu____10733 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____10733))
                  in
               let lecs1 =
                 let uu____10744 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____10797 = univs_and_uvars_of_lec this_lec  in
                        match uu____10797 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____10744 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____10902 = lec_hd  in
                   match uu____10902 with
                   | (lbname,e,c) ->
                       let uu____10912 =
                         let uu____10918 =
                           let uu____10920 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____10922 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____10924 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____10920 uu____10922 uu____10924
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____10918)
                          in
                       let uu____10928 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____10912 uu____10928
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____10947 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____10947 with
                         | FStar_Pervasives_Native.Some uu____10956 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____10964 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____10968 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____10968 with
                              | (bs,kres) ->
                                  ((let uu____11012 =
                                      let uu____11013 =
                                        let uu____11016 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____11016
                                         in
                                      uu____11013.FStar_Syntax_Syntax.n  in
                                    match uu____11012 with
                                    | FStar_Syntax_Syntax.Tm_type uu____11017
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____11021 =
                                          let uu____11023 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____11023  in
                                        if uu____11021
                                        then fail1 kres
                                        else ()
                                    | uu____11028 -> fail1 kres);
                                   (let a =
                                      let uu____11030 =
                                        let uu____11033 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _11036  ->
                                             FStar_Pervasives_Native.Some
                                               _11036) uu____11033
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____11030
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____11044 ->
                                          let uu____11053 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____11053
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
                      (fun uu____11156  ->
                         match uu____11156 with
                         | (lbname,e,c) ->
                             let uu____11202 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____11263 ->
                                   let uu____11276 = (e, c)  in
                                   (match uu____11276 with
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
                                                (fun uu____11316  ->
                                                   match uu____11316 with
                                                   | (x,uu____11322) ->
                                                       let uu____11323 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____11323)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____11341 =
                                                let uu____11343 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____11343
                                                 in
                                              if uu____11341
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
                                          let uu____11352 =
                                            let uu____11353 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____11353.FStar_Syntax_Syntax.n
                                             in
                                          match uu____11352 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____11378 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____11378 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____11389 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____11393 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____11393, gen_tvars))
                                in
                             (match uu____11202 with
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
        (let uu____11540 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____11540
         then
           let uu____11543 =
             let uu____11545 =
               FStar_List.map
                 (fun uu____11560  ->
                    match uu____11560 with
                    | (lb,uu____11569,uu____11570) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____11545 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____11543
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____11596  ->
                match uu____11596 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____11625 = gen env is_rec lecs  in
           match uu____11625 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____11724  ->
                       match uu____11724 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____11786 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____11786
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____11834  ->
                           match uu____11834 with
                           | (l,us,e,c,gvs) ->
                               let uu____11868 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____11870 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____11872 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____11874 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____11876 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____11868 uu____11870 uu____11872
                                 uu____11874 uu____11876))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____11921  ->
                match uu____11921 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____11965 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____11965, t, c, gvs)) univnames_lecs
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
              (let uu____12026 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____12026 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____12032 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _12035  -> FStar_Pervasives_Native.Some _12035)
                     uu____12032)
             in
          let is_var e1 =
            let uu____12043 =
              let uu____12044 = FStar_Syntax_Subst.compress e1  in
              uu____12044.FStar_Syntax_Syntax.n  in
            match uu____12043 with
            | FStar_Syntax_Syntax.Tm_name uu____12048 -> true
            | uu____12050 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1473_12071 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1473_12071.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1473_12071.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____12072 -> e2  in
          let env2 =
            let uu___1476_12074 = env1  in
            let uu____12075 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1476_12074.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1476_12074.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1476_12074.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1476_12074.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1476_12074.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1476_12074.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1476_12074.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1476_12074.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1476_12074.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1476_12074.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1476_12074.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1476_12074.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1476_12074.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1476_12074.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1476_12074.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1476_12074.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1476_12074.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____12075;
              FStar_TypeChecker_Env.is_iface =
                (uu___1476_12074.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1476_12074.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1476_12074.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1476_12074.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1476_12074.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1476_12074.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1476_12074.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1476_12074.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1476_12074.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1476_12074.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1476_12074.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1476_12074.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1476_12074.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1476_12074.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1476_12074.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1476_12074.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1476_12074.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1476_12074.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1476_12074.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1476_12074.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1476_12074.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1476_12074.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1476_12074.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1476_12074.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1476_12074.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1476_12074.FStar_TypeChecker_Env.strict_args_tab)
            }  in
          let uu____12077 = check1 env2 t1 t2  in
          match uu____12077 with
          | FStar_Pervasives_Native.None  ->
              let uu____12084 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____12090 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____12084 uu____12090
          | FStar_Pervasives_Native.Some g ->
              ((let uu____12097 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12097
                then
                  let uu____12102 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____12102
                else ());
               (let uu____12108 = decorate e t2  in (uu____12108, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____12136 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____12136
         then
           let uu____12139 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____12139
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____12153 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____12153 with
         | (c,g_c) ->
             let uu____12165 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____12165
             then
               let uu____12173 =
                 let uu____12175 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____12175  in
               (uu____12173, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____12183 =
                    let uu____12184 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____12184
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____12183
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____12185 = check_trivial_precondition env c1  in
                match uu____12185 with
                | (ct,vc,g_pre) ->
                    ((let uu____12201 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____12201
                      then
                        let uu____12206 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____12206
                      else ());
                     (let uu____12211 =
                        let uu____12213 =
                          let uu____12214 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____12214  in
                        discharge uu____12213  in
                      let uu____12215 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____12211, uu____12215)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_12249 =
        match uu___8_12249 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____12259)::[] -> f fst1
        | uu____12284 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____12296 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____12296
          (fun _12297  -> FStar_TypeChecker_Common.NonTrivial _12297)
         in
      let op_or_e e =
        let uu____12308 =
          let uu____12309 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____12309  in
        FStar_All.pipe_right uu____12308
          (fun _12312  -> FStar_TypeChecker_Common.NonTrivial _12312)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _12319  -> FStar_TypeChecker_Common.NonTrivial _12319)
         in
      let op_or_t t =
        let uu____12330 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____12330
          (fun _12333  -> FStar_TypeChecker_Common.NonTrivial _12333)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _12340  -> FStar_TypeChecker_Common.NonTrivial _12340)
         in
      let short_op_ite uu___9_12346 =
        match uu___9_12346 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____12356)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____12383)::[] ->
            let uu____12424 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____12424
              (fun _12425  -> FStar_TypeChecker_Common.NonTrivial _12425)
        | uu____12426 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____12438 =
          let uu____12446 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____12446)  in
        let uu____12454 =
          let uu____12464 =
            let uu____12472 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____12472)  in
          let uu____12480 =
            let uu____12490 =
              let uu____12498 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____12498)  in
            let uu____12506 =
              let uu____12516 =
                let uu____12524 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____12524)  in
              let uu____12532 =
                let uu____12542 =
                  let uu____12550 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____12550)  in
                [uu____12542; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____12516 :: uu____12532  in
            uu____12490 :: uu____12506  in
          uu____12464 :: uu____12480  in
        uu____12438 :: uu____12454  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____12612 =
            FStar_Util.find_map table
              (fun uu____12627  ->
                 match uu____12627 with
                 | (x,mk1) ->
                     let uu____12644 = FStar_Ident.lid_equals x lid  in
                     if uu____12644
                     then
                       let uu____12649 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____12649
                     else FStar_Pervasives_Native.None)
             in
          (match uu____12612 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____12653 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____12661 =
      let uu____12662 = FStar_Syntax_Util.un_uinst l  in
      uu____12662.FStar_Syntax_Syntax.n  in
    match uu____12661 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____12667 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____12703)::uu____12704 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____12723 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____12732,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____12733))::uu____12734 -> bs
      | uu____12752 ->
          let uu____12753 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____12753 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____12757 =
                 let uu____12758 = FStar_Syntax_Subst.compress t  in
                 uu____12758.FStar_Syntax_Syntax.n  in
               (match uu____12757 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____12762) ->
                    let uu____12783 =
                      FStar_Util.prefix_until
                        (fun uu___10_12823  ->
                           match uu___10_12823 with
                           | (uu____12831,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____12832)) ->
                               false
                           | uu____12837 -> true) bs'
                       in
                    (match uu____12783 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____12873,uu____12874) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____12946,uu____12947) ->
                         let uu____13020 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____13040  ->
                                   match uu____13040 with
                                   | (x,uu____13049) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____13020
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____13098  ->
                                     match uu____13098 with
                                     | (x,i) ->
                                         let uu____13117 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____13117, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____13128 -> bs))
  
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
            let uu____13157 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____13157
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
          let uu____13188 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____13188
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
        (let uu____13231 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____13231
         then
           ((let uu____13236 = FStar_Ident.text_of_lid lident  in
             d uu____13236);
            (let uu____13238 = FStar_Ident.text_of_lid lident  in
             let uu____13240 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____13238 uu____13240))
         else ());
        (let fv =
           let uu____13246 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____13246
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
         let uu____13258 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1633_13260 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1633_13260.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1633_13260.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1633_13260.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1633_13260.FStar_Syntax_Syntax.sigattrs)
           }), uu____13258))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_13278 =
        match uu___11_13278 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____13281 -> false  in
      let reducibility uu___12_13289 =
        match uu___12_13289 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____13296 -> false  in
      let assumption uu___13_13304 =
        match uu___13_13304 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____13308 -> false  in
      let reification uu___14_13316 =
        match uu___14_13316 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____13319 -> true
        | uu____13321 -> false  in
      let inferred uu___15_13329 =
        match uu___15_13329 with
        | FStar_Syntax_Syntax.Discriminator uu____13331 -> true
        | FStar_Syntax_Syntax.Projector uu____13333 -> true
        | FStar_Syntax_Syntax.RecordType uu____13339 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____13349 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____13362 -> false  in
      let has_eq uu___16_13370 =
        match uu___16_13370 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____13374 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____13453 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____13460 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____13471 =
        let uu____13473 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___17_13479  ->
                  match uu___17_13479 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____13482 -> false))
           in
        FStar_All.pipe_right uu____13473 Prims.op_Negation  in
      if uu____13471
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____13503 =
            let uu____13509 =
              let uu____13511 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____13511 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____13509)  in
          FStar_Errors.raise_error uu____13503 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____13529 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____13537 =
            let uu____13539 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____13539  in
          if uu____13537 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____13549),uu____13550) ->
              ((let uu____13562 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____13562
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____13571 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____13571
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____13582 ->
              let uu____13591 =
                let uu____13593 =
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
                Prims.op_Negation uu____13593  in
              if uu____13591 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____13603 ->
              let uu____13610 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____13610 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____13618 ->
              let uu____13625 =
                let uu____13627 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____13627  in
              if uu____13625 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____13637 ->
              let uu____13638 =
                let uu____13640 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____13640  in
              if uu____13638 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13650 ->
              let uu____13651 =
                let uu____13653 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____13653  in
              if uu____13651 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13663 ->
              let uu____13676 =
                let uu____13678 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____13678  in
              if uu____13676 then err'1 () else ()
          | uu____13688 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let has_erased_for_extraction_attr fv =
        let uu____13711 =
          let uu____13716 =
            FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
          FStar_All.pipe_right uu____13716
            (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
           in
        FStar_All.pipe_right uu____13711
          (fun l_opt  ->
             (FStar_Util.is_some l_opt) &&
               (let uu____13735 = FStar_All.pipe_right l_opt FStar_Util.must
                   in
                FStar_All.pipe_right uu____13735
                  (FStar_List.existsb
                     (fun t1  ->
                        let uu____13753 =
                          let uu____13754 = FStar_Syntax_Subst.compress t1
                             in
                          uu____13754.FStar_Syntax_Syntax.n  in
                        match uu____13753 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            FStar_Ident.lid_equals
                              (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              FStar_Parser_Const.must_erase_for_extraction_attr
                            -> true
                        | uu____13760 -> false))))
         in
      let rec aux_whnf env t1 =
        let uu____13786 =
          let uu____13787 = FStar_Syntax_Subst.compress t1  in
          uu____13787.FStar_Syntax_Syntax.n  in
        match uu____13786 with
        | FStar_Syntax_Syntax.Tm_type uu____13791 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (has_erased_for_extraction_attr fv)
        | FStar_Syntax_Syntax.Tm_arrow uu____13794 ->
            let uu____13809 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____13809 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____13842 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____13842
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____13848;
               FStar_Syntax_Syntax.index = uu____13849;
               FStar_Syntax_Syntax.sort = t2;_},uu____13851)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____13860,uu____13861) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____13903::[]) ->
            let uu____13942 =
              let uu____13943 = FStar_Syntax_Util.un_uinst head1  in
              uu____13943.FStar_Syntax_Syntax.n  in
            (match uu____13942 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.erased_lid)
                   || (has_erased_for_extraction_attr fv)
             | uu____13948 -> false)
        | uu____13950 -> false
      
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
        (let uu____13960 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____13960
         then
           let uu____13965 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____13965
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
                  let uu____14026 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____14026 r  in
                let uu____14036 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____14036 with
                | (uu____14045,signature) ->
                    let uu____14047 =
                      let uu____14048 = FStar_Syntax_Subst.compress signature
                         in
                      uu____14048.FStar_Syntax_Syntax.n  in
                    (match uu____14047 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14056) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____14104 =
                                FStar_List.fold_left
                                  (fun uu____14143  ->
                                     fun uu____14144  ->
                                       match (uu____14143, uu____14144) with
                                       | ((is,g,substs),(b,uu____14191)) ->
                                           let uu____14220 =
                                             let uu____14233 =
                                               FStar_Syntax_Subst.subst
                                                 substs
                                                 b.FStar_Syntax_Syntax.sort
                                                in
                                             new_implicit_var "" r env
                                               uu____14233
                                              in
                                           (match uu____14220 with
                                            | (t,uu____14246,g_t) ->
                                                let uu____14260 =
                                                  FStar_TypeChecker_Env.conj_guard
                                                    g g_t
                                                   in
                                                ((FStar_List.append is [t]),
                                                  uu____14260,
                                                  (FStar_List.append substs
                                                     [FStar_Syntax_Syntax.NT
                                                        (b, t)]))))
                                  ([], FStar_TypeChecker_Env.trivial_guard,
                                    [FStar_Syntax_Syntax.NT
                                       ((FStar_Pervasives_Native.fst a),
                                         a_tm)]) bs2
                                 in
                              (match uu____14104 with
                               | (is,g,uu____14281) ->
                                   let repr =
                                     let uu____14291 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts [u]
                                        in
                                     FStar_All.pipe_right uu____14291
                                       FStar_Pervasives_Native.snd
                                      in
                                   let uu____14300 =
                                     let uu____14301 =
                                       let uu____14306 =
                                         FStar_List.map
                                           FStar_Syntax_Syntax.as_arg (a_tm
                                           :: is)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr
                                         uu____14306
                                        in
                                     uu____14301 FStar_Pervasives_Native.None
                                       r
                                      in
                                   (uu____14300, g))
                          | uu____14315 -> fail1 signature)
                     | uu____14316 -> fail1 signature)
  
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
  
let (layered_effect_indices_as_binders :
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binders)
  =
  fun sig_ts  ->
    fun u  ->
      fun a_tm  ->
        let uu____14364 = FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]
           in
        match uu____14364 with
        | (uu____14369,sig_tm) ->
            let uu____14371 =
              let uu____14372 = FStar_Syntax_Subst.compress sig_tm  in
              uu____14372.FStar_Syntax_Syntax.n  in
            (match uu____14371 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14376) ->
                 let bs1 = FStar_Syntax_Subst.open_binders bs  in
                 (match bs1 with
                  | (a',uu____14399)::bs2 ->
                      FStar_All.pipe_right bs2
                        (FStar_Syntax_Subst.subst_binders
                           [FStar_Syntax_Syntax.NT (a', a_tm)])
                  | uu____14421 -> failwith "Impossible!")
             | uu____14423 -> failwith "Impossible")
  